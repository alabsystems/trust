use super::*;
use crate::{CommandSpec, Delegations, Descriptor, GnuTransport, JobBinding, Status, StatusFrame};

pub(crate) fn request() -> Request {
    Request {
        root: b"/sdk".to_vec(),
        member: crate::Request {
            binding: JobBinding {
                session: "s-abcd".into(),
                root_attempt: [1; 16],
                capability: [2; 32],
            },
            member_attempt: [3; 16],
            role: Role::MachOLinker(Loan { parent_attempt: [4; 16], nonce: [5; 16], cpu_slot: 0 }),
            command: CommandSpec {
                program: b"/sdk/bin/rust-lld".to_vec(),
                arg0: None,
                args: [
                    b"-flavor".as_slice(),
                    b"darwin",
                    b"--threads=1",
                    b"--thinlto-jobs=1",
                    b"--read-workers=0",
                ]
                .iter()
                .map(|s| s.to_vec())
                .collect(),
                environment: vec![],
                cwd: b"/work".to_vec(),
            },
            delegations: Delegations {
                cpu: Some(Descriptor { source: 5, target: 5 }),
                gnu: GnuTransport::None,
                fences: vec![],
            },
            timeout_ns: None,
        },
    }
}
pub(crate) fn prepared(request: &Request) -> Prepared {
    Prepared {
        root_attempt: request.member.binding.root_attempt,
        member_attempt: request.member.member_attempt,
        loan: request.loan().unwrap(),
        identity: Identity { pid: 100, birth: 200, birth_kind: BirthKind::MacosWallMicroseconds },
        root: request.root.clone(),
        policy: "observed-native-policy".into(),
        scope: "original-held-inputs".into(),
        executable: MetadataFile {
            path: request.member.command.program.clone(),
            sha256: [7; 32],
            bytes: 4096,
            device: 1,
            inode: 2,
        },
        runtime: vec![],
        loader_paths: vec![b"/sdk/lib".to_vec()],
        system_dependencies: vec!["/usr/lib/libSystem.B.dylib".into()],
        host: "host".into(),
        boot: "boot".into(),
    }
}
pub(crate) fn completion(request: &Request) -> Completion {
    Completion {
        loan: request.loan().unwrap(),
        completed: MetadataCompletion {
            finished: StatusFrame {
                root_attempt: request.member.binding.root_attempt,
                member_attempt: request.member.member_attempt,
                status: Status::Finished {
                    outcome: crate::Outcome::Exit(0),
                    cause: crate::CompletionCause::Exited,
                    runtime_ns: 10,
                },
            },
            inputs_unchanged: Ok(()),
        },
        observation: crate::accounting::Observation::uncollected(),
    }
}
#[test]
fn direct_linker_refuses_runtime_plugins_and_opaque_llvm_options() {
    let plain = request();
    plain.validate().unwrap();
    for controls in [
        vec![b"--load-pass-plugin".to_vec(), b"/foreign/pass.dylib".to_vec()],
        vec![b"--load-pass-plugin=/foreign/pass.dylib".to_vec()],
        vec![b"-mllvm".to_vec(), b"-load=/foreign/pass.dylib".to_vec()],
        vec![b"-mllvm=-load=/foreign/pass.dylib".to_vec()],
    ] {
        let mut wrong = plain.clone();
        wrong.member.command.args.splice(2..2, controls);
        // Existing generic Role4 syntax remains unchanged; the new direct
        // purpose must not treat a held main image as plugin input custody.
        wrong.member.validate().unwrap();
        assert!(wrong.validate().is_err(), "unowned runtime/opaque LLVM input accepted");
    }
    for controls in [
        vec![b"-force_load".to_vec(), b"/work/static.a".to_vec()],
        vec![b"-lto_library".to_vec(), b"/work/obsolete-ignored.dylib".to_vec()],
    ] {
        let mut supported = plain.clone();
        supported.member.command.args.splice(2..2, controls);
        supported.validate().unwrap();
    }
}
#[test]
fn direct_linker_request_is_distinct_and_retains_exact_parent_primary() {
    let request = request();
    assert!(Request::decode(&request.member.encode().unwrap()).is_err());
    assert!(Request::decode(&request.encode().unwrap()).unwrap() == request);
    for mutate in 0..6 {
        let mut wrong = request.clone();
        match mutate {
            0 => wrong.member.role = Role::Compile,
            1 => wrong.member.delegations.cpu = None,
            2 => wrong.root = b"/another-sdk".to_vec(),
            3 => wrong.member.command.args.push(b"--threads=8".to_vec()),
            4 => wrong.member.delegations.cpu.as_mut().unwrap().target = 3,
            _ => wrong.member.command.arg0 = Some(b"another-driver".to_vec()),
        }
        assert!(wrong.encode().is_err());
    }
    let mut bytes = request.encode().unwrap();
    bytes.push(0);
    assert!(Request::decode(&bytes).is_err());
}
#[test]
fn direct_linker_preparation_cannot_rebind_parent_nonce_slot_or_sdk() {
    let request = request();
    let original = prepared(&request);
    let encoded = original.encode().unwrap();
    assert_eq!(Prepared::decode(&encoded, &request).unwrap(), original);
    for mutate in 0..6 {
        let mut wrong = request.clone();
        let Role::MachOLinker(mut loan) = wrong.member.role else { unreachable!() };
        match mutate {
            0 => loan.parent_attempt = [9; 16],
            1 => loan.nonce = [9; 16],
            2 => loan.cpu_slot = 1,
            3 => wrong.member.member_attempt = [9; 16],
            4 => wrong.member.binding.root_attempt = [9; 16],
            _ => {
                wrong.root = b"/other".to_vec();
                wrong.member.command.program = b"/other/bin/rust-lld".to_vec();
            }
        }
        wrong.member.role = Role::MachOLinker(loan);
        assert!(Prepared::decode(&encoded, &wrong).is_err());
    }
}
#[test]
fn direct_linker_inventory_rejects_duplicate_objects_and_escaped_loader_roots() {
    let request = request();
    let original = prepared(&request);
    let mut wrong = original.clone();
    let mut alias = wrong.executable.clone();
    alias.path = b"/sdk/lib/alias.dylib".to_vec();
    wrong.runtime.push(alias);
    assert!(wrong.encode().is_err());
    let mut wrong = original.clone();
    wrong.loader_paths = vec![b"/sdk-elsewhere/lib".to_vec()];
    assert!(wrong.encode().is_err());
    let mut wrong = original;
    wrong.identity.birth = 0;
    assert!(wrong.encode().is_err());
}
#[test]
fn direct_linker_completion_requires_owning_wait_and_preserves_uncollected_metrics() {
    let request = request();
    let original = completion(&request);
    assert!(Completion::decode(&original.completed.encode().unwrap(), &request).is_err());
    let decoded = Completion::decode(&original.encode().unwrap(), &request).unwrap();
    assert_eq!(decoded, original);
    assert_eq!(decoded.observation.cpu_times, None);
    assert_eq!(decoded.observation.peak_rss_bytes, None);
    let mut wrong = request.clone();
    let Role::MachOLinker(mut loan) = wrong.member.role else { unreachable!() };
    loan.nonce = [6; 16];
    wrong.member.role = Role::MachOLinker(loan);
    assert!(Completion::decode(&original.encode().unwrap(), &wrong).is_err());
}
