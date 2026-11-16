// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use crate::*;

/// Darwin's F_GETFL exposes FMARK/FDEFER while Unix-socket GC marks original
/// SCM_RIGHTS fileglobs. These are kernel GC state, not caller status flags:
/// XNU kern_descrip.c F_GETFL returns OFLAGS(f_flag), and uipc_usrreq.c unp_gc
/// toggles 0x1000/0x2000 independently. Exclude only those two bits on Darwin;
/// retain every caller-controlled/unknown bit and all independent FD checks.
#[cfg(feature = "channel")]
pub(crate) fn caller_status_flags(flags: i32) -> i32 {
    #[cfg(target_os = "macos")]
    {
        flags & !(0x1000 | 0x2000)
    }
    #[cfg(not(target_os = "macos"))]
    {
        flags
    }
}

#[cfg(all(unix, feature = "channel"))]
#[test]
fn status_flag_comparison_never_hides_a_nonblocking_change() {
    assert_ne!(caller_status_flags(0), caller_status_flags(libc::O_NONBLOCK));
    #[cfg(target_os = "macos")]
    {
        assert_eq!(caller_status_flags(0), caller_status_flags(0x1000 | 0x2000));
        assert_ne!(caller_status_flags(0), caller_status_flags(0x1000 | 0x2000 | libc::O_NONBLOCK));
    }
}
fn request() -> Request {
    Request {
        binding: JobBinding {
            session: "s-abcd".into(),
            root_attempt: [1; 16],
            capability: [2; 32],
        },
        member_attempt: [3; 16],
        role: Role::Compile,
        command: CommandSpec {
            program: b"/sdk/trustc".to_vec(),
            arg0: Some(b"trustc".to_vec()),
            args: vec![vec![b'a', 0xff]],
            environment: vec![(b"KEY".to_vec(), vec![0xfe])],
            cwd: b"/source".to_vec(),
        },
        delegations: Delegations {
            cpu: Some(Descriptor { source: 5, target: 3 }),
            gnu: GnuTransport::NamedFifo {
                locator: b"/private/tokens".to_vec(),
                device: 1,
                inode: 2,
                read: Descriptor { source: 6, target: 4 },
                write: Descriptor { source: 7, target: 5 },
            },
            fences: vec![],
        },
        timeout_ns: Some(100),
    }
}
#[test]
fn request_preserves_os_bytes_named_transport_and_refuses_ambiguous_input() {
    let original = request();
    let bytes = original.encode().unwrap();
    assert!(Request::decode(&bytes).unwrap() == original);
    for end in 0..bytes.len() {
        assert!(Request::decode(&bytes[..end]).is_err());
    }
    let mut extra = bytes.clone();
    extra.push(0);
    assert!(Request::decode(&extra).is_err());
    let mut invalid = request();
    invalid.delegations.cpu.as_mut().unwrap().source = CONTROL_FD;
    assert!(invalid.encode().is_err());
    let mut invalid = request();
    invalid.command.environment.push(invalid.command.environment[0].clone());
    assert!(invalid.encode().is_err());
    let mut invalid = request();
    invalid.delegations.gnu = GnuTransport::None;
    assert!(invalid.encode().is_err());
    let mut invalid = request();
    invalid.binding.session = format!("s-{}", "a".repeat(63));
    assert!(invalid.encode().is_err());
    let mut invalid = request();
    invalid.member_attempt = invalid.binding.root_attempt;
    assert!(invalid.encode().is_err());
}
#[test]
fn a_session_is_an_aterm_tab_id_in_either_form() {
    for good in ["tqn5r6e0148", "t0000000000", "s-abcd", "s-0123456789abcdef0123"] {
        let mut req = request();
        req.binding.session = good.into();
        assert!(req.encode().is_ok(), "{good}");
    }
    for bad in [
        "tqn5r6e014",
        "tqn5r6e01488",
        "tqn5r6e014i",
        "tqn5r6e014u",
        "tQN5R6E0148",
        "t",
        "s-",
        "s-ABCD",
        "x0123456789",
    ] {
        let mut req = request();
        req.binding.session = bad.into();
        assert!(req.encode().is_err(), "{bad}");
    }
}
#[test]
fn metadata_probes_require_exact_bounded_queries_and_existing_cpu_only() {
    let mut probe = request();
    probe.role = Role::MetadataProbe;
    probe.delegations.gnu = GnuTransport::None;
    probe.timeout_ns = Some(8_000_000_000);
    for query in [b"--print=sysroot".as_slice(), b"--print=target-list"] {
        probe.command.args = vec![query.to_vec()];
        assert!(Request::decode(&probe.encode().unwrap()).unwrap() == probe);
    }
    for args in [
        vec![b"--print=cfg".to_vec()],
        vec![b"--print=sysroot".to_vec(), b"--emit=link".to_vec()],
        vec![b"@/private/response".to_vec()],
    ] {
        let mut invalid = probe.clone();
        invalid.command.args = args;
        assert!(invalid.encode().is_err());
    }
    for timeout in [None, Some(0), Some(8_000_000_001)] {
        let mut invalid = probe.clone();
        invalid.timeout_ns = timeout;
        assert!(invalid.encode().is_err());
    }
    let mut invalid = probe.clone();
    invalid.delegations.cpu = None;
    assert!(invalid.encode().is_err());
    let mut invalid = probe.clone();
    invalid.delegations.fences.push(Descriptor { source: 8, target: 8 });
    assert!(invalid.encode().is_err());
    let mut invalid = probe;
    invalid.delegations.gnu = request().delegations.gnu;
    assert!(invalid.encode().is_err());
}
fn started() -> Started {
    Started {
        identity: Identity { pid: 42, birth: 123, birth_kind: BirthKind::MacosWallMicroseconds },
        monotonic_ns: 2,
        unix_ns: 3,
    }
}
#[test]
fn lifecycle_and_cancellation_are_bound_and_unknown_keeps_execution_facts() {
    let outcomes = [
        Status::Attached,
        Status::Started(started()),
        Status::Finished {
            outcome: Outcome::Signal(9),
            cause: CompletionCause::ResourceLimit,
            runtime_ns: 7,
        },
        Status::Finished {
            outcome: Outcome::Signal(9),
            cause: CompletionCause::HostFault,
            runtime_ns: 7,
        },
        Status::Refused { reason: "before launch".into() },
        Status::Unknown { reason: "lost terminal".into(), started: Some(started()) },
    ];
    for status in outcomes {
        let frame = StatusFrame { root_attempt: [1; 16], member_attempt: [3; 16], status };
        let encoded = frame.encode().unwrap();
        assert_eq!(StatusFrame::decode(&encoded, [1; 16], [3; 16]).unwrap(), frame);
        assert!(StatusFrame::decode(&encoded, [1; 16], [4; 16]).is_err());
        let mut trailing = encoded.clone();
        trailing.push(0);
        assert!(StatusFrame::decode(&trailing, [1; 16], [3; 16]).is_err());
    }
    let cancel = Cancel { root_attempt: [1; 16], member_attempt: [3; 16] };
    assert_eq!(Cancel::decode(&cancel.encode().unwrap(), cancel).unwrap(), cancel);
    let mut invalid = started();
    invalid.identity.pid = 1;
    assert!(
        StatusFrame {
            root_attempt: [1; 16],
            member_attempt: [3; 16],
            status: Status::Started(invalid)
        }
        .encode()
        .is_err()
    );
}
#[test]
fn producer_answer_matches_one_pending_call_and_actual_helper_identity() {
    let proof = ProducerChallenge {
        root_attempt: [1; 16],
        member_attempt: [3; 16],
        helper: started().identity,
        nonce: [5; 32],
    };
    assert!(ProducerChallenge::decode(&proof.encode().unwrap()).unwrap() == proof);
    assert!(proof.verify_answer(&proof.answer().unwrap()).is_ok());
    assert!(proof.verify_answer(&proof.encode().unwrap()).is_err());
    let mut other = proof.clone();
    other.helper.birth += 1;
    assert!(proof.verify_answer(&other.answer().unwrap()).is_err());
    let mut other = proof.clone();
    other.member_attempt = [4; 16];
    assert!(proof.verify_answer(&other.answer().unwrap()).is_err());
}
#[cfg(all(feature = "channel", any(target_os = "linux", target_os = "macos")))]
#[test]
fn framed_channel_bounds_partial_input_and_poisoning() {
    use std::io::Write;
    use std::os::unix::net::UnixStream;
    use std::time::{Duration, Instant};
    let (a, b) = UnixStream::pair().unwrap();
    let mut a = Channel::new(a).unwrap();
    let mut b = Channel::new(b).unwrap();
    assert!(!b.ready_to_receive().unwrap());
    let payload = request().encode().unwrap();
    a.send(&payload, Instant::now() + Duration::from_secs(1)).unwrap();
    assert_eq!(b.receive(Instant::now() + Duration::from_secs(1)).unwrap(), payload);
    let (mut raw, read) = UnixStream::pair().unwrap();
    let mut read = Channel::new(read).unwrap();
    raw.write_all(&[0, 0, 0, 5, 1]).unwrap();
    drop(raw);
    assert!(read.receive(Instant::now() + Duration::from_secs(1)).is_err());
    assert!(read.poisoned());
    assert!(read.receive(Instant::now() + Duration::from_secs(1)).is_err());
    let (a, b) = UnixStream::pair().unwrap();
    let mut a = Channel::new(a).unwrap();
    drop(b);
    assert!(a.send(b"closed", Instant::now() + Duration::from_secs(1)).is_err());
    assert!(a.poisoned());
}

#[cfg(all(feature = "channel", any(target_os = "linux", target_os = "macos")))]
#[test]
fn closed_peer_is_safe_with_default_sigpipe() {
    const CHILD: &str = "TRUST_CONTROLLER_SIGPIPE_FIXTURE";
    if std::env::var_os(CHILD).is_some() {
        use std::os::unix::net::UnixStream;
        use std::time::{Duration, Instant};
        // SAFETY: this dedicated reexecuted fixture process owns its signal
        // disposition; restore POSIX default to detect a missing MSG_NOSIGNAL.
        assert_ne!(unsafe { libc::signal(libc::SIGPIPE, libc::SIG_DFL) }, libc::SIG_ERR);
        let (stream, peer) = UnixStream::pair().unwrap();
        drop(peer);
        let mut channel = Channel::new(stream).unwrap();
        assert!(channel.send(b"closed", Instant::now() + Duration::from_secs(1)).is_err());
        return;
    }
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "tests::closed_peer_is_safe_with_default_sigpipe"])
        .env(CHILD, "1")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "default SIGPIPE killed controller fixture: {:?}\nstdout: {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn context_uses_one_original_claim_and_only_exact_root_can_request_initial_cpu() {
    let query = ContextQuery { binding: request().binding, call_attempt: [9; 16] };
    let original_root = started().identity;
    let context = Context {
        session: query.binding.session.clone(),
        root_attempt: query.binding.root_attempt,
        host: "apple:host".into(),
        boot: "abcd".into(),
        original_root,
        subject: Subject::Root { identity: original_root },
        cpu: Cpu::CooperativeShared {
            ceiling: 28,
            native_manifest: FileIdentity { device: 1, inode: 10 },
        },
        memory: Memory {
            bytes: 1 << 30,
            namespace: [1; 16],
            marker: "1-42-1".into(),
            epoch: [2; 16],
            guard: FileIdentity { device: 1, inode: 11 },
        },
        sdk: None,
    };
    let mut reply = ContextReply { call_attempt: query.call_attempt, context };
    let bytes = reply.encode().unwrap();
    assert_eq!(ContextReply::decode(&bytes, &query).unwrap(), reply);
    assert!(ContextReply::decode(&bytes[..bytes.len() - 8], &query).is_err());
    reply.context.sdk = Some(SdkCustody {
        execution: b"/private/sdk".to_vec(),
        build: 42,
        lease_path: b"/private/leases/42".to_vec(),
        lease: FileIdentity { device: 1, inode: 90 },
        inherited_fd: 19,
    });
    let sdk_bytes = reply.encode().unwrap();
    assert_eq!(ContextReply::decode(&sdk_bytes, &query).unwrap(), reply);
    reply.context.sdk.as_mut().unwrap().inherited_fd = 1;
    assert!(reply.encode().is_err());
    reply.context.sdk = None;
    assert!(reply.context.may_acquire_initial_cpu(original_root));
    let mut nested = original_root;
    nested.pid += 1;
    assert!(!reply.context.may_acquire_initial_cpu(nested));
    reply.context.subject = Subject::RegisteredMember { identity: nested, attempt: [8; 16] };
    assert!(!reply.context.may_acquire_initial_cpu(nested));
    let member = ContextReply::decode(&reply.encode().unwrap(), &query).unwrap();
    assert_eq!(member.context.memory.bytes, 1 << 30);
    assert_eq!(member.context.memory.guard, reply.context.memory.guard);
    reply.context.subject = Subject::Root { identity: original_root };
    reply.context.cpu =
        Cpu::RetainedFixed { units: 28, native_manifest: FileIdentity { device: 1, inode: 10 } };
    assert!(!reply.context.may_acquire_initial_cpu(original_root));
    let mut wrong = query.clone();
    wrong.call_attempt = [7; 16];
    assert!(ContextReply::decode(&bytes, &wrong).is_err());
    reply.context.memory.guard.inode = 0;
    assert!(reply.encode().is_err());
}
#[test]
fn context_routing_and_private_locator_refuse_noncanonical_or_cross_role_input() {
    let binding = request().binding;
    let locator = binding.locator().unwrap();
    assert!(JobBinding::from_locator(&locator).unwrap() == binding);
    assert!(JobBinding::from_locator(&(locator.clone() + ":extra")).is_err());
    assert!(JobBinding::from_locator(&locator.replacen("s-abcd", "s-ABCD", 1)).is_err());
    let query = ContextQuery { binding, call_attempt: [9; 16] };
    let encoded = query.encode().unwrap();
    assert!(ContextQuery::decode(&encoded).unwrap() == query);
    assert!(matches!(Call::decode(&encoded).unwrap(), Call::Context(_)));
    assert!(Request::decode(&encoded).is_err());
    assert!(matches!(Call::decode(&request().encode().unwrap()).unwrap(), Call::Member(_)));
    let mut trailing = encoded.clone();
    trailing.push(0);
    assert!(Call::decode(&trailing).is_err());
    for end in 0..encoded.len() {
        assert!(ContextQuery::decode(&encoded[..end]).is_err());
    }
}

#[test]
fn helper_fd_locators_are_canonical_and_disjoint_from_sources_not_targets() {
    let fds = HelperFds { control: 19, producer: 23 };
    let args = fds.arguments().unwrap();
    assert_eq!(HelperFds::parse(&args).unwrap(), Some(fds));
    assert_eq!(
        HelperFds::parse(&HELPER_ARGUMENTS.map(Into::into)).unwrap(),
        Some(HelperFds::default())
    );
    assert!(fds.validate_delegations(&request().delegations).is_ok());
    let mut req = request();
    req.delegations.cpu.as_mut().unwrap().source = 19;
    assert!(fds.validate_delegations(&req.delegations).is_err());
    let mut invalid = args.clone();
    invalid[2] = "--control-fd=019".into();
    assert!(HelperFds::parse(&invalid).is_err());
    let mut invalid = args.clone();
    invalid[3] = "--producer-fd=19".into();
    assert!(HelperFds::parse(&invalid).is_err());
    assert!(HelperFds::parse(&["ordinary-command".into()]).unwrap().is_none());
    let mut invalid = args;
    invalid.push("extra".into());
    assert!(HelperFds::parse(&invalid).is_err());
}

#[test]
fn context_unavailable_is_bound_observation_denial_not_execution_refusal() {
    let query = ContextQuery { binding: request().binding, call_attempt: [9; 16] };
    let unavailable =
        ContextUnavailable::for_query(&query, "original custody unavailable".into()).unwrap();
    let bytes = ContextResponse::Unavailable(unavailable.clone()).encode().unwrap();
    assert_eq!(
        ContextResponse::decode(&bytes, &query).unwrap(),
        ContextResponse::Unavailable(unavailable)
    );
    assert!(StatusFrame::decode(&bytes, query.binding.root_attempt, query.call_attempt).is_err());
    let mut wrong = query.clone();
    wrong.call_attempt = [8; 16];
    assert!(ContextResponse::decode(&bytes, &wrong).is_err());
    let mut extra = bytes;
    extra.push(0);
    assert!(ContextResponse::decode(&extra, &query).is_err());
    assert!(ContextUnavailable::for_query(&query, "".into()).is_err());
}

#[test]
fn telemetry_preserves_unknown_zero_and_original_age_and_rejects_cross_call_or_role() {
    let query = TelemetryQuery {
        query: ContextQuery { binding: request().binding, call_attempt: [9; 16] },
    };
    assert!(TelemetryQuery::decode(&query.encode().unwrap()).unwrap() == query);
    let original_root =
        Identity { pid: 42, birth: 100, birth_kind: BirthKind::MacosWallMicroseconds };
    let context = ContextReply {
        call_attempt: query.query.call_attempt,
        context: Context {
            session: query.query.binding.session.clone(),
            root_attempt: query.query.binding.root_attempt,
            host: "apple:host".into(),
            boot: "abcd".into(),
            original_root,
            subject: Subject::Root { identity: original_root },
            cpu: Cpu::CooperativeShared {
                ceiling: 28,
                native_manifest: FileIdentity { device: 1, inode: 10 },
            },
            memory: Memory {
                bytes: 1 << 30,
                namespace: [1; 16],
                marker: "1-42-1".into(),
                epoch: [2; 16],
                guard: FileIdentity { device: 1, inode: 11 },
            },
            sdk: None,
        },
    };
    let mut reply = TelemetryReply {
        context,
        snapshot: Snapshot {
            cpus: 28,
            busy_millicores: None,
            available_memory_bytes: Some(0),
            pressure: Pressure::Critical,
            thermal: Thermal::Unknown,
            sample_age_ns: 7_000_000_000,
            window_ns: 0,
        },
    };
    let bytes = reply.encode().unwrap();
    assert_eq!(
        TelemetryResponse::decode(&bytes, &query).unwrap(),
        TelemetryResponse::Ready(Box::new(reply.clone()))
    );
    assert!(ContextResponse::decode(&bytes, &query.query).is_err());
    assert!(
        StatusFrame::decode(&bytes, query.query.binding.root_attempt, query.query.call_attempt)
            .is_err()
    );
    let mut wrong = query.clone();
    wrong.query.call_attempt = [8; 16];
    assert!(TelemetryResponse::decode(&bytes, &wrong).is_err());
    let mut trailing = bytes;
    trailing.push(0);
    assert!(TelemetryResponse::decode(&trailing, &query).is_err());
    reply.snapshot.busy_millicores = Some(0);
    assert!(reply.encode().is_err()); // no valid CPU interval, even for zero busy
    reply.snapshot.window_ns = 1_000_000_000;
    reply.snapshot.busy_millicores = Some(28_001);
    assert!(reply.encode().is_err());
    reply.snapshot.busy_millicores = Some(28_000);
    assert!(reply.encode().is_ok());
    let denied = TelemetryResponse::Unavailable(
        ContextUnavailable::for_query(&query.query, "custody unavailable".into()).unwrap(),
    );
    assert_eq!(TelemetryResponse::decode(&denied.encode().unwrap(), &query).unwrap(), denied);
}

mod loan;
