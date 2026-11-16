// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

use std::os::fd::{AsFd, AsRawFd};
use std::os::unix::net::UnixStream;

use super::*;

#[test]
fn capture_uses_the_actual_socket_and_preserves_original_flags() {
    let (stream, _peer) = UnixStream::pair().expect("native socket pair");
    // SAFETY: This test owns and retains the socket; both calls only observe it.
    let before = unsafe { libc::fcntl(stream.as_raw_fd(), libc::F_GETFL) };
    assert!(before >= 0);
    let peer = CapturedPeer::capture(stream.as_fd()).expect("kernel audit token");
    assert_eq!(peer.pid(), std::process::id());
    // SAFETY: geteuid reads only this process's effective account identity.
    assert_eq!(peer.uid(), unsafe { libc::geteuid() });
    let identity = crate::process::read_identity(peer.pid()).expect("original native identity");
    assert_eq!(peer.exec_version(), identity.exec_version);
    // SAFETY: The same original socket remains held and this only reads flags.
    assert_eq!(unsafe { libc::fcntl(stream.as_raw_fd(), libc::F_GETFL) }, before);
    assert!(!peer.matches_native_token(&[0; 32]));
}

#[test]
fn a_regular_file_cannot_supply_peer_code_identity() {
    let file = tempfile::tempfile().expect("owned file");
    assert!(matches!(CapturedPeer::capture(file.as_fd()), Err(Error::Unchecked(_))));
}

#[test]
fn native_requirement_compilation_rejects_invalid_policy_syntax() {
    assert!(Requirement::compile("not a valid ( requirement").is_err());
    let (_, text) = Requirement::compile("identifier \"com.aterm.provenance-test\"")
        .expect("actual native requirement parser");
    assert!(text.contains("com.aterm.provenance-test"));
}

#[test]
fn definite_code_refusal_is_distinct_from_operational_uncertainty() {
    assert_eq!(darwin::static_validity(0), Ok(()));
    assert_eq!(darwin::guest_validity(0), Ok(()));
    for code in [-67062, -67061, -67050] {
        assert!(matches!(darwin::static_validity(code), Err(Error::Refused(_))));
        assert!(matches!(darwin::guest_validity(code), Err(Error::Refused(_))));
    }
    for code in [-67063, -67034] {
        assert!(matches!(darwin::guest_validity(code), Err(Error::Refused(_))));
        assert!(matches!(darwin::static_validity(code), Err(Error::Unchecked(_))));
    }
    for code in [-67060, -67068, -67048, -67032, -67033, -67025, -67006, -67056, -67054, -67045, -1]
    {
        assert!(matches!(darwin::static_validity(code), Err(Error::Unchecked(_))));
        assert!(matches!(darwin::guest_validity(code), Err(Error::Unchecked(_))));
    }
}

#[test]
fn actual_captured_guest_meets_its_requirement_and_refuses_foreign_code() {
    let (stream, _peer) = UnixStream::pair().expect("original connected peer");
    let captured = CapturedPeer::capture(stream.as_fd()).expect("actual kernel peer");
    let (own, _) = Requirement::current().expect("this running image's requirement");
    captured.check(&own).expect("actual guest meets its own native requirement");
    let (foreign, _) =
        Requirement::compile("identifier \"com.aterm.provenance.deliberately-foreign-image\"")
            .expect("independent mismatching native requirement");
    assert!(matches!(captured.check(&foreign), Err(Error::Refused(_))));
}
