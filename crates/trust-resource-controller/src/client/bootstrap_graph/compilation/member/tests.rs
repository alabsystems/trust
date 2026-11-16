//! DATA restrictions only: no fake Full/Host/SDK or completion constructors.
use super::*;
use crate::bootstrap_graph::compilation::tests::{advanced, member};
use crate::{CompletionCause, Outcome};

fn retirement(request: &MemberRequest) -> RetireRequest {
    RetireRequest { key: request.key.clone(), sequence: request.sequence, member: request.member }
}
#[test]
fn one_use_booking_keeps_spent_sequences_and_nonces_across_retirement() {
    let request = member();
    let mut state = Members::default();
    state.begin(&request).unwrap();
    assert!(state.begin(&request).is_err());
    let mut duplicate = request.clone();
    duplicate.sequence += 1;
    assert!(state.begin(&duplicate).is_err());
    let mut foreign = retirement(&request);
    foreign.member = [99; 16];
    assert!(state.completed(&foreign).is_err());
    state.completed(&retirement(&request)).unwrap();
    assert!(state.active.is_empty());
    assert!(state.begin(&request).is_err());
    assert!(state.begin(&duplicate).is_err());
    let mut fresh = duplicate;
    fresh.member = [23; 16];
    fresh.sequence = 7; // Real BeforeRequest gaps are allowed, never rollback.
    state.begin(&fresh).unwrap();
    assert_eq!(state.active.len(), 1);
    let mut earlier = fresh;
    earlier.sequence = 6;
    earlier.member = [24; 16];
    assert!(state.begin(&earlier).is_err());
}
#[test]
fn handshake_terminal_or_foreign_status_never_substitutes_for_owning_retirement() {
    let request = member();
    let frame = |status, root, nonce| {
        StatusFrame { root_attempt: root, member_attempt: nonce, status }.encode().unwrap()
    };
    let root = request.key.attempt.key.graph.query.binding.root_attempt;
    let attached = frame(Status::Attached, root, request.member);
    assert!(member_status(&request, &attached, false).is_err());
    assert_eq!(member_status(&request, &attached, true).unwrap(), Status::Attached);
    let refused = frame(
        Status::Refused { reason: "unsupported private producer".into() },
        root,
        request.member,
    );
    assert!(matches!(member_status(&request, &refused, false).unwrap(), Status::Refused { .. }));
    let finished = frame(
        Status::Finished {
            outcome: Outcome::Exit(0),
            cause: CompletionCause::Exited,
            runtime_ns: 1,
        },
        root,
        request.member,
    );
    assert!(member_status(&request, &finished, true).is_err());
    let unknown = frame(
        Status::Unknown { reason: "custody missing".into(), started: None },
        root,
        request.member,
    );
    assert!(member_status(&request, &unknown, true).is_err());
    for (root, nonce) in [([99; 16], request.member), (root, [99; 16])] {
        assert!(member_status(&request, &frame(Status::Attached, root, nonce), true).is_err());
    }
}
#[test]
fn member_roles_require_same_original_full_key_gnu_and_held_seed_selection() {
    let value = advanced();
    let request = member();
    same_member_bindings(&value, &request).unwrap();
    for mutation in 0..5 {
        let mut changed = request.clone();
        match mutation {
            0 => changed.key.compilation = [99; 16],
            1 => changed.key.attempt.key.operation = [99; 16],
            2 => changed.command.program = b"/control-sdk/bin/trustc".to_vec(),
            3 => changed.program = ProgramRole::SeedTargo,
            _ => {
                changed.gnu = crate::bootstrap_graph::GnuIdentity::NumericPipe {
                    read: crate::FileIdentity { device: 77, inode: 88 },
                    write: crate::FileIdentity { device: 77, inode: 99 },
                }
            }
        }
        assert!(same_member_bindings(&value, &changed).is_err());
    }
    // Syntax/equality alone cannot issue this role: actual Host producer custody
    // is still required. This test constructs DATA, never an execution owner.
    let mut issued = request;
    issued.program = ProgramRole::IssuedProgram { producer: [99; 16], artifact: 0 };
    same_member_bindings(&value, &issued).unwrap();
}

#[test]
fn actual_transfer_closes_local_output_writers_on_attachment_and_unknown_delivery() {
    use std::fs::{File, OpenOptions};
    use std::io::{Read as _, Write as _};
    use std::os::fd::{AsRawFd as _, FromRawFd as _};
    use std::os::unix::fs::MetadataExt as _;
    use std::os::unix::net::UnixStream;

    use crate::FileIdentity;
    use crate::bootstrap_graph::GnuIdentity;

    let pipe = || {
        let mut raw = [-1; 2];
        assert_eq!(unsafe { libc::pipe(raw.as_mut_ptr()) }, 0);
        let fds = raw.map(|fd| unsafe { OwnedFd::from_raw_fd(fd) });
        for fd in &fds {
            assert_eq!(unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, libc::FD_CLOEXEC) }, 0);
        }
        fds
    };
    for unknown in [false, true] {
        let deadline = Instant::now() + Duration::from_secs(10);
        let [mut output, writer] = pipe().map(File::from);
        let stdio = [
            File::open("/dev/null").unwrap().into(),
            writer.into(),
            OpenOptions::new().write(true).open("/dev/null").unwrap().into(),
        ];
        let gnu = pipe();
        let identity = |fd: &OwnedFd| {
            let m = File::from(fd.try_clone().unwrap()).metadata().unwrap();
            FileIdentity { device: m.dev(), inode: m.ino() }
        };
        let mut request = member();
        request.gnu =
            GnuIdentity::NumericPipe { read: identity(&gnu[0]), write: identity(&gnu[1]) };
        let expected = request.clone();
        let (client, server) = UnixStream::pair().unwrap();
        let peer = client.try_clone().unwrap();
        let identity =
            trust_resource_provenance::process::read_identity(std::process::id()).unwrap();
        let server = std::thread::spawn(move || {
            let mut channel = Channel::new(server).unwrap();
            assert_eq!(channel.receive(deadline).unwrap(), expected.hello().unwrap());
            assert!(
                MemberRequest::decode(&channel.receive(deadline).unwrap()).unwrap() == expected
            );
            channel.send(&[RIGHTS_MARKER], deadline).unwrap();
            let [stdin, stdout, stderr, read, write] =
                transport::receive(&mut channel, &expected, deadline, || Ok(())).unwrap();
            File::from(stdout).write_all(b"actual bytes").unwrap();
            drop((stdin, stderr, read, write));
            if !unknown {
                channel
                    .send(
                        &StatusFrame {
                            root_attempt: expected.key.attempt.key.graph.query.binding.root_attempt,
                            member_attempt: expected.member,
                            status: Status::Attached,
                        }
                        .encode()
                        .unwrap(),
                        deadline,
                    )
                    .unwrap();
                crate::runtime_input_retention::transport::finish_reply(&mut channel).unwrap();
                assert_eq!(channel.receive(deadline).unwrap(), [1]);
            }
            // This is a transport-only peer, never a fake Full/SDK/issuer.
        });
        let mut channel = Channel::new(client).unwrap();
        let result = deliver(&mut channel, &request, stdio, &gnu, deadline, || {
            trust_resource_provenance::process::check_peer(&peer, identity)
        });
        assert_eq!(result.is_err(), unknown);
        server.join().unwrap();
        let mut bytes = [0; 12];
        output.read_exact(&mut bytes).unwrap();
        assert_eq!(&bytes, b"actual bytes");
        let mut poll = libc::pollfd { fd: output.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        assert_eq!(unsafe { libc::poll(&mut poll, 1, 1000) }, 1);
        assert_ne!(
            poll.revents & libc::POLLHUP,
            0,
            "a local transfer writer still holds output open"
        );
        assert_eq!(output.read(&mut bytes).unwrap(), 0);
        assert!(gnu.iter().all(|fd| unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) } >= 0));
    }
}

#[test]
fn retirement_rejects_every_original_identity_alias() {
    let request = member();
    let key = &request.key.attempt.key;
    for alias in [
        [0; 16],
        request.key.compilation,
        key.operation,
        key.graph.graph,
        key.graph.query.call_attempt,
        key.graph.query.binding.root_attempt,
    ] {
        let mut changed = retirement(&request);
        changed.member = alias;
        assert!(changed.encode().is_err());
    }
}

#[test]
fn full_close_book_is_idle_only_after_same_members_are_settled() {
    let request = member();
    let mut members = Members::default();
    assert!(members.idle());
    members.begin(&request).unwrap();
    assert!(!members.idle());
    let mut foreign = retirement(&request);
    foreign.member = [77; 16];
    assert!(members.completed(&foreign).is_err());
    assert!(!members.idle());
    members.completed(&retirement(&request)).unwrap();
    assert!(members.idle());
}
