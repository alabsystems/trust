//! Transport-only controls. These regular files are not domain claims/SDKs.
use std::io::Seek as _;
use std::os::unix::fs::{FileExt as _, PermissionsExt};

use super::*;

const TEST: &str =
    "handoff::fixed_tests::fixed_courier_crosses_unaware_descendants_with_original_rights";
const MODE: &str = "TRUST_FIXED_COURIER_TEST_MODE";

#[test]
fn fixed_courier_crosses_unaware_descendants_with_original_rights() {
    if std::env::var_os(MODE).is_none() {
        assert!(
            std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", TEST, "--nocapture"])
                .env(MODE, "owner")
                .status()
                .unwrap()
                .success()
        );
        return;
    }
    if let Some(mode) = std::env::var_os(MODE).filter(|mode| mode != "owner") {
        if mode == "relay" {
            assert!(
                std::process::Command::new(std::env::current_exe().unwrap())
                    .args(["--exact", TEST, "--nocapture"])
                    .env(MODE, "receive")
                    .status()
                    .unwrap()
                    .success()
            );
        } else {
            let ad = std::env::var_os(super::super::FIXED_CLAIM_HANDOFF_ENV).unwrap();
            assert!(recover_cpu_resources(&ad).is_err());
            assert!(recover_named_fifo_resources(&ad).is_err());
            let (packet, originals) = recover_fixed_claim(&ad).unwrap();
            let packet = std::fs::File::from(packet);
            let mut bytes = vec![0; packet.metadata().unwrap().len() as usize];
            packet.read_exact_at(&mut bytes, 0).unwrap();
            assert_eq!(bytes, b"fixed packet DATA only");
            assert_eq!(originals.len(), 129, "complete multi-message population");
            for fd in &originals {
                assert_ne!(
                    unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) } & libc::FD_CLOEXEC,
                    0
                );
            }
            let original = std::fs::File::from(originals.into_iter().next().unwrap());
            original.try_lock().unwrap();
            let probe = std::fs::OpenOptions::new()
                .read(true)
                .write(true)
                .open(std::env::var_os("TRUST_FIXED_COURIER_TEST_FILE").unwrap())
                .unwrap();
            assert!(matches!(probe.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
            for fd in [packet.as_raw_fd(), original.as_raw_fd()] {
                assert_ne!(unsafe { libc::fcntl(fd, libc::F_GETFD) } & libc::FD_CLOEXEC, 0);
            }
        }
        return;
    }
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("original");
    let original = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&path)
        .unwrap();
    original.try_lock().unwrap();
    let mut packet = tempfile::tempfile().unwrap();
    packet.write_all(b"fixed packet DATA only").unwrap();
    let mut cursor = packet.try_clone().unwrap();
    let before = cursor.stream_position().unwrap();
    let originals = (0..129).map(|_| original.try_clone().unwrap().into()).collect();
    let endpoint = FixedClaimHandoff::new(packet.into(), originals).unwrap();
    drop(original);
    let status = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", TEST, "--nocapture"])
        .env(MODE, "relay")
        .env(super::super::FIXED_CLAIM_HANDOFF_ENV, endpoint.advertisement())
        .env("TRUST_FIXED_COURIER_TEST_FILE", &path)
        .status()
        .unwrap();
    assert!(status.success());
    assert_eq!(
        cursor.stream_position().unwrap(),
        before,
        "courier read moved the original OFD cursor"
    );
    drop(endpoint);
    std::fs::OpenOptions::new().read(true).write(true).open(path).unwrap().try_lock().unwrap();
}

#[test]
fn fixed_role_rejects_missing_or_unsafe_files_without_becoming_cpu_or_gnu() {
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("original");
    let original = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&path)
        .unwrap();
    let packet = || {
        let mut f = tempfile::tempfile().unwrap();
        f.write_all(b"packet DATA").unwrap();
        f
    };
    assert!(FixedClaimHandoff::new(packet().into(), vec![]).is_err());
    original.set_permissions(std::fs::Permissions::from_mode(0o666)).unwrap();
    assert!(
        FixedClaimHandoff::new(packet().into(), vec![original.try_clone().unwrap().into()])
            .is_err()
    );
    original.set_permissions(std::fs::Permissions::from_mode(0o600)).unwrap();
    let endpoint = FixedClaimHandoff::new(packet().into(), vec![original.into()]).unwrap();
    let parsed = Advertisement::parse_role(endpoint.advertisement(), Role::FixedClaim).unwrap();
    assert_eq!(parsed.pair, [2, 0]);
    assert!(Advertisement::parse_role(endpoint.advertisement(), Role::CpuBundle).is_err());
    assert!(Advertisement::parse(endpoint.advertisement()).is_err());
}

#[test]
fn incomplete_multimessage_or_bad_final_response_closes_the_accumulated_originals() {
    const CHILD: &str = "TRUST_FIXED_COURIER_FAILURE_TEST_CHILD";
    if std::env::var_os(CHILD).is_none() {
        assert!(std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact","handoff::fixed_tests::incomplete_multimessage_or_bad_final_response_closes_the_accumulated_originals","--nocapture"])
            .env(CHILD,"1").status().unwrap().success());
        return;
    }
    for mode in ["missing-tail", "short-tail", "bad-challenge", "trailing-data"] {
        let temporary = tempfile::tempdir().unwrap();
        let path = temporary.path().join("original");
        let original = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)
            .unwrap();
        original.try_lock().unwrap();
        let mut packet = tempfile::tempfile().unwrap();
        packet.write_all(b"transport DATA only").unwrap();
        let mut handles = vec![OwnedFd::from(packet)];
        handles.extend((0..129).map(|_| OwnedFd::from(original.try_clone().unwrap())));
        let (mut sender, mut receiver) = UnixStream::pair().unwrap();
        sender.set_nonblocking(true).unwrap();
        receiver.set_nonblocking(true).unwrap();
        let deadline = Instant::now() + TIMEOUT;
        send_handles(&sender, &handles[..128], deadline).unwrap();
        match mode {
            "missing-tail" => {}
            "short-tail" => send_handles(&sender, &handles[128..129], deadline).unwrap(),
            _ => {
                send_handles(&sender, &handles[128..], deadline).unwrap();
                sender
                    .write_all(if mode == "bad-challenge" { &[8; 32] } else { &[9; 32] })
                    .unwrap();
                if mode == "trailing-data" {
                    sender.write_all(b"x").unwrap();
                }
            }
        }
        sender.shutdown(std::net::Shutdown::Write).unwrap();
        drop(sender);
        drop(handles);
        drop(original);
        assert!(
            receive_role_response(&mut receiver, deadline, Role::FixedClaim, 130, &[9; 32])
                .is_err(),
            "{mode}"
        );
        drop(receiver);
        let probe = std::fs::OpenOptions::new().read(true).write(true).open(&path).unwrap();
        probe.try_lock().unwrap_or_else(|e| panic!("{mode} leaked a received original: {e}"));
    }
}
