// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::os::unix::net::UnixStream;

use trust_resource_provenance::process;

use super::*;

#[test]
fn reply_eof_keeps_actual_peer_alive_through_validation_before_ack() {
    for foreign in [false, true] {
        let (client, server) = UnixStream::pair().unwrap();
        let peer = client.try_clone().unwrap();
        let deadline = Instant::now() + Duration::from_secs(60);
        let (retire_peer, retain_peer) = std::sync::mpsc::sync_channel(0);
        let server = std::thread::spawn(move || {
            let mut channel = Channel::new(server).unwrap();
            channel.send(b"transport-only observation", deadline).unwrap();
            crate::runtime_input_retention::transport::finish_reply(&mut channel).unwrap();
            let result = channel.receive(deadline);
            // Keep this actual peer alive until the client's explicit teardown.
            // ACK may already have arrived: racing its close against the test's
            // write shutdown produces Darwin ENOTCONN, unrelated to validation.
            retain_peer.recv().unwrap();
            result
        });
        let mut channel = Channel::new(client).unwrap();
        assert_eq!(channel.receive(deadline).unwrap(), b"transport-only observation");
        let mut expected = process::read_identity(std::process::id()).unwrap();
        if foreign {
            expected.birth ^= 1;
        }
        let result = finish_reply(&mut channel, deadline, || process::check_peer(&peer, expected));
        assert_eq!(result.is_ok(), !foreign);
        crate::runtime_input_retention::transport::finish_reply(&mut channel).unwrap();
        retire_peer.send(()).unwrap();
        let ack = server.join().unwrap();
        if foreign {
            assert!(ack.is_err(), "failed provenance must not acknowledge the reply");
        } else {
            assert_eq!(ack.unwrap(), [1]);
        }
    }
}

#[cfg(target_os = "macos")]
#[test]
fn fully_closed_reply_loses_darwin_peer_credentials() {
    let (client, server) = UnixStream::pair().unwrap();
    let peer = client.try_clone().unwrap();
    let deadline = Instant::now() + Duration::from_secs(60);
    let server = std::thread::spawn(move || {
        Channel::new(server).unwrap().send(b"closed reply", deadline).unwrap();
    });
    server.join().unwrap();
    let mut channel = Channel::new(client).unwrap();
    assert_eq!(channel.receive(deadline).unwrap(), b"closed reply");
    let expected = process::read_identity(std::process::id()).unwrap();
    assert!(finish_reply(&mut channel, deadline, || process::check_peer(&peer, expected)).is_err());
}
