use super::*;
use crate::{Call, CommandSpec, Delegations, Descriptor, JobBinding};

pub(crate) fn registration() -> Registration {
    Registration {
        key: Key {
            root_attempt: [1; 16],
            invocation_sha256: [2; 32],
            phase: [4; 16],
            ordinal: 3,
            output: [5; 16],
        },
        program: InputFile { path: b"/outputs/debug/harness".to_vec(), sha256: [6; 32] },
        runtime_roots: vec![b"/outputs/debug/deps".to_vec()],
        producer_attempt: Some([7; 16]),
    }
}
pub(crate) fn request() -> ProducedRequest {
    let registration = registration();
    ProducedRequest {
        member: Request {
            binding: JobBinding {
                session: "s-ab".into(),
                root_attempt: [1; 16],
                capability: [9; 32],
            },
            member_attempt: [8; 16],
            role: Role::WorkloadProduced,
            command: CommandSpec {
                program: registration.program.path.clone(),
                arg0: None,
                args: vec![b"--list".to_vec()],
                cwd: b"/source".to_vec(),
                environment: vec![(b"LANG".to_vec(), b"C".to_vec())],
            },
            delegations: Delegations { cpu: None, gnu: GnuTransport::None, fences: vec![] },
            timeout_ns: Some(30_000_000_000),
        },
        key: registration.key,
        kind: MemberKind::Inventory,
        program_sha256: registration.program.sha256,
        runtime_roots: registration.runtime_roots,
    }
}
pub(crate) fn prepared() -> ProducedPrepared {
    let request = request();
    ProducedPrepared {
        key: request.key,
        member_attempt: request.member.member_attempt,
        identity: Identity { pid: 42, birth: 12, birth_kind: BirthKind::MacosWallMicroseconds },
        output_root: b"/outputs".to_vec(),
        sdk_root: b"/sdk".to_vec(),
        policy: INPUT_POLICY.into(),
        scope: INPUT_SCOPE.into(),
        executable: MetadataFile {
            path: request.member.command.program,
            sha256: request.program_sha256,
            bytes: 100,
            device: 1,
            inode: 2,
        },
        runtime: vec![
            MetadataFile {
                path: b"/sdk/lib/runtime.dylib".to_vec(),
                sha256: [3; 32],
                bytes: 40,
                device: 1,
                inode: 3,
            },
            MetadataFile {
                path: b"/outputs/debug/deps/dep.dylib".to_vec(),
                sha256: [4; 32],
                bytes: 40,
                device: 1,
                inode: 4,
            },
        ],
        loader_paths: vec![
            b"/outputs/debug".to_vec(),
            b"/outputs/debug/deps".to_vec(),
            b"/sdk/lib".to_vec(),
        ],
        system_dependencies: vec!["/usr/lib/libSystem.B.dylib".into()],
        host: "fixture-host".into(),
        boot: "fixture-boot".into(),
    }
}

#[test]
fn produced_envelopes_bind_exact_registration_kind_and_real_phase_ordinal() {
    let registration = registration();
    assert_eq!(Registration::decode(&registration.encode().unwrap()).unwrap(), registration);
    let request = request();
    assert!(ProducedRequest::decode(&request.encode().unwrap()).unwrap() == request);
    request.validate_registered(&registration).unwrap();
    let mut changed = request.clone();
    changed.key.ordinal += 1;
    assert!(changed.validate_registered(&registration).is_err());
    changed = request.clone();
    changed.program_sha256 = [11; 32];
    assert!(changed.validate_registered(&registration).is_err());
    changed = request.clone();
    changed.runtime_roots.push(b"/outputs/other".to_vec());
    assert!(changed.validate_registered(&registration).is_err());
    let ack = RegistrationAck { key: registration.key.clone(), executable: prepared().executable };
    assert_eq!(RegistrationAck::decode(&ack.encode().unwrap(), &registration).unwrap(), ack);
    assert!(ProducedRequest::decode(&ack.encode().unwrap()).is_err());
    assert!(Registration::decode(&request.encode().unwrap()).is_err());
    let refused = RegistrationReply::Refused {
        key: registration.key.clone(),
        reason: "actual original output is unavailable".into(),
    };
    assert_eq!(
        RegistrationReply::decode(&refused.encode().unwrap(), &registration).unwrap(),
        refused
    );
    assert_eq!(
        RegistrationAck::decode(&refused.encode().unwrap(), &registration).unwrap_err().kind(),
        io::ErrorKind::PermissionDenied
    );
    let mut foreign = registration.clone();
    foreign.key.ordinal += 1;
    assert!(RegistrationReply::decode(&refused.encode().unwrap(), &foreign).is_err());
    let mut trailing = registration.encode().unwrap();
    trailing.push(0);
    assert!(Registration::decode(&trailing).is_err());
}

#[test]
fn role7_cannot_enter_legacy_proxy_or_fabricate_new_cpu_gnu_or_query_authority() {
    let request = request();
    assert!(!request.member.role.is_proxy_member());
    assert!(Call::Member(Box::new(request.member.clone())).encode().is_err());
    assert!(
        crate::accounting::AccountedRequest {
            request: request.member.clone(),
            scope: crate::accounting::Scope::ChildAndWaitedDescendantsV1
        }
        .encode()
        .is_err()
    );
    for variant in 0..6 {
        let mut changed = request.clone();
        match variant {
            0 => changed.member.delegations.cpu = Some(Descriptor { source: 6, target: 6 }),
            1 => {
                changed.member.delegations.gnu = GnuTransport::NumericPipe {
                    read: Descriptor { source: 7, target: 3 },
                    write: Descriptor { source: 8, target: 4 },
                }
            }
            2 => changed.member.delegations.fences.push(Descriptor { source: 9, target: 9 }),
            3 => changed.kind = MemberKind::CompilerQuery,
            4 => changed.member.command.args = vec![b"--print=sysroot".to_vec()],
            _ => changed.member.timeout_ns = None,
        }
        assert!(changed.encode().is_err(), "variant{variant}");
    }
    let mut script = request.clone();
    script.kind = MemberKind::BuildScript;
    script.member.command.args.clear();
    script.validate().unwrap();
    let mut sample = request.clone();
    sample.kind = MemberKind::Sample;
    sample.member.command.args = vec![b"--test-threads=1".to_vec()];
    sample.validate().unwrap();
}

#[test]
fn mixed_inventory_keeps_every_original_root_and_rejects_aliases_escape_and_bad_policies() {
    let request = request();
    let prepared = prepared();
    assert_eq!(ProducedPrepared::decode(&prepared.encode().unwrap(), &request).unwrap(), prepared);
    for changed in 0..10 {
        let mut bad = prepared.clone();
        match changed {
            0 => bad.runtime[0].path = b"/sdk-other/lib/a.dylib".to_vec(),
            1 => bad.sdk_root = b"/outputs/nested".to_vec(),
            2 => bad.runtime[0].inode = bad.executable.inode,
            3 => bad.policy = "native-metadata/macho-arm64-sysroot-rpath-v1".into(),
            4 => bad.key.ordinal += 1,
            5 => bad.member_attempt = [9; 16],
            6 => bad.runtime[1].bytes = MAX_IMAGE_BYTES + 1,
            7 => bad.loader_paths.push(b"/elsewhere".to_vec()),
            8 => {
                bad.loader_paths.remove(1);
            }
            _ => bad.system_dependencies = vec!["/other/runtime.dylib".into()],
        }
        assert!(bad.validate_for(&request).is_err(), "variant{changed}");
    }
    let mut frame = prepared.encode().unwrap();
    frame[16..24].copy_from_slice(&1u64.to_be_bytes());
    assert!(
        ProducedPrepared::decode(&frame, &request).is_err(),
        "registration cannot masquerade as preparation"
    );
}

#[test]
fn produced_counts_flags_and_bounds_refuse_before_allocating_untrusted_populations() {
    let mut registration = registration();
    registration.runtime_roots = vec![b"/outputs/deps".to_vec(); MAX_RUNTIME_ROOTS + 1];
    assert!(registration.encode().is_err());
    let mut registration = super::tests::registration();
    registration.producer_attempt = Some([0; 16]);
    assert!(registration.encode().is_err());
    let mut bytes = super::tests::registration().encode().unwrap();
    let size = bytes.len();
    bytes[size - 24..size - 16].copy_from_slice(&2u64.to_be_bytes());
    assert!(Registration::decode(&bytes).is_err(), "nonbinary optional flag");
    let mut prepared = prepared();
    prepared.runtime = vec![prepared.runtime[0].clone(); MAX_IMAGES + 1];
    assert!(prepared.encode().is_err());
}

#[cfg(feature = "client")]
#[test]
fn producing_data_policy_labels_match_actual_maintained_native_input_profile() {
    assert_eq!(INPUT_POLICY, trust_resource_provenance::program::produced::RUNTIME_POLICY);
    assert_eq!(INPUT_SCOPE, trust_resource_provenance::program::INPUT_SCOPE);
}

#[test]
fn caller_environment_cannot_override_original_scheduling_sdk_or_loader_custody() {
    for name in [
        b"MAKEFLAGS".as_slice(),
        b"CARGO_MAKEFLAGS",
        b"MFLAGS",
        b"CARGO_JOBSERVER_HANDOFF",
        b"TRUST_JOBSERVER_HANDOFF",
        b"TRUST_CPU_HANDOFF",
        b"ATERM_RESOURCE_JOB_V3",
        b"ATERM_RESOURCE_INSPECTOR",
        b"PARENT_SESSION_ID",
        b"ATERM_SDK_LEASE_V3",
        b"ATERM_WORKLOAD_HOST_STORE_FD_V1",
        b"ATERM_WORKLOAD_CPU_FDS_V1",
        b"BUILD_SLOT_CPU_PROTOCOL",
        b"DYLD_LIBRARY_PATH",
        b"LD_PRELOAD",
        b"dyld_insert_libraries",
    ] {
        let mut request = request();
        request.member.command.environment.push((name.to_vec(), b"caller-selected".to_vec()));
        assert!(request.encode().is_err(), "protected {}", String::from_utf8_lossy(name));
    }
    let mut request = request();
    for (name, value) in [
        (b"NUM_JOBS".as_slice(), b"7".as_slice()),
        (b"CARGO", b"/sdk/bin/targo"),
        (b"RUSTC", b"/sdk/bin/trustc"),
        (b"CARGO_MANIFEST_DIR", b"/source"),
        (b"OUT_DIR", b"/outputs/script"),
        (b"DEP_INPUT_ROOT", b"/dependency"),
        (b"TRUST_SPEC_SRC", b"/spec"),
    ] {
        request.member.command.environment.push((name.to_vec(), value.to_vec()));
    }
    request.validate().unwrap();
    assert!(ProducedRequest::decode(&request.encode().unwrap()).unwrap() == request);
}
