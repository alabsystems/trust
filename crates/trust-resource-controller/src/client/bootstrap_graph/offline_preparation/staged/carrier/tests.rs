//! Actual Unix carrier ordering only. Canonical packet DATA constructs no
//! Host, live Root/Graph, namespace, source/program/SDK or retirement owner.
use std::os::unix::net::UnixStream;
use std::sync::mpsc;
use std::thread;
use super::*;

#[test]
fn native_reservation_waits_for_selection_on_the_same_carrier_before_eof_ack() {
    let query = ProgramSelectionQuery {
        key: crate::bootstrap_graph::query::tests::request().key,
    };
    query.key.validate().unwrap();
    let reservation = ReservedPrograms { query: query.clone(),
        namespace: b"/output/private-child".to_vec(), remaining_root_ns: 2_000_000_000 };
    let selection = ProgramSelection { key: query.key.clone(),
        configured_targo: b"/output/private-child/bin/cargo".to_vec(),
        configured_compiler: b"/output/private-child/bin/trustc".to_vec() };
    let reply = ProgramSelectionReply { selection: selection.clone(),
        namespace: reservation.namespace.clone(), remaining_root_ns: 1_000_000_000 };
    let (client, server) = UnixStream::pair().unwrap();
    let deadline = Instant::now() + Duration::from_secs(3);
    let (release, retained_peer) = mpsc::channel();
    let expected_query = query.clone(); let expected_selection = selection.clone();
    let sent_reservation = reservation.clone(); let sent_reply = reply.clone();
    let peer = thread::spawn(move || -> io::Result<()> {
        let mut channel = Channel::new(server)?;
        let result = (|| {
            if channel.receive(deadline)? != expected_query.hello()? {
                return Err(crate::wire::invalid());
            }
            if ProgramSelectionQuery::decode(&channel.receive(deadline)?)? != expected_query {
                return Err(crate::wire::invalid());
            }
            channel.send(&sent_reservation.encode()?, deadline)?;
            // This is the actual native handler's next read, not an EOF.
            let actual = ProgramSelection::decode(&channel.receive(deadline)?)?;
            if actual != expected_selection { return Err(crate::wire::invalid()); }
            channel.send(&sent_reply.encode()?, deadline)?;
            crate::runtime_input_retention::transport::finish_reply(&mut channel)?;
            if channel.receive(deadline)? != [1] { return Err(crate::wire::invalid()); }
            Ok(())
        })();
        // An ACK permits the fixture peer to finish; keep it intact through
        // caller postchecks instead of racing teardown with the last send.
        let _ = retained_peer.recv_timeout(Duration::from_secs(1));
        result
    });
    let mut channel = Channel::new(client).unwrap();
    let result = (|| {
        let actual = reserve(&mut channel, &query, deadline)?;
        if actual != reservation { return Err(crate::wire::invalid()); }
        reservation_boundary(&mut channel, deadline, || Ok(()))?;
        let actual = select(&mut channel, &selection, deadline)?;
        preparation::finish_reply(&mut channel, deadline, || Ok(()))?;
        Ok(actual)
    })();
    let _ = release.send(());
    let native = peer.join().expect("native wire fixture panicked");
    assert!(result.is_ok(), "same carrier must reach selection before EOF: {:?}", result.as_ref().err());
    assert!(result.unwrap() == reply);
    native.expect("native wire contract refused the client sequence");
}

#[test]
fn malformed_foreign_and_lost_reservation_reply_permanently_poison_actual_carrier() {
    for mode in 0..3 {
        let query = ProgramSelectionQuery { key: crate::bootstrap_graph::query::tests::request().key };
        let expected = query.clone();
        let mut foreign = ReservedPrograms { query: query.clone(),
            namespace: b"/output/private-child".to_vec(), remaining_root_ns: 1_000_000_000 };
        foreign.query.key.operation = [91; 16];
        let (client, server) = UnixStream::pair().unwrap();
        let deadline = Instant::now() + Duration::from_secs(3);
        let peer = thread::spawn(move || -> io::Result<()> {
            let mut channel = Channel::new(server)?;
            if channel.receive(deadline)? != expected.hello()? { return Err(crate::wire::invalid()); }
            if ProgramSelectionQuery::decode(&channel.receive(deadline)?)? != expected {
                return Err(crate::wire::invalid());
            }
            match mode {
                0 => channel.send(&[0], deadline)?,
                1 => channel.send(&foreign.encode()?, deadline)?,
                _ => {} // physical EOF before any reservation frame
            }
            Ok(())
        });
        let mut channel = Channel::new(client).unwrap();
        assert!(reserve(&mut channel, &query, deadline).is_err());
        assert!(channel.poisoned());
        assert!(channel.send(b"replacement attempt", deadline).is_err());
        peer.join().unwrap().unwrap();
    }
}

#[test]
fn reservation_boundary_postcheck_and_original_expiry_never_recover_or_require_peer_eof() {
    for mode in 0..3 {
        let (client, _same_open_peer) = UnixStream::pair().unwrap();
        let mut channel = Channel::new(client).unwrap();
        let deadline = if mode == 0 { Instant::now() - Duration::from_nanos(1) }
            else { Instant::now() + Duration::from_millis(20) };
        let mut checked = false;
        let error = reservation_boundary(&mut channel, deadline, || {
            checked = true;
            if mode == 1 { return Err(io::Error::other("original peer/source refused")); }
            thread::sleep(deadline.saturating_duration_since(Instant::now()) + Duration::from_millis(1));
            Ok(())
        }).unwrap_err();
        assert_eq!(checked, mode != 0);
        if mode != 1 { assert_eq!(error.kind(), io::ErrorKind::TimedOut); }
        assert!(channel.poisoned());
        assert!(channel.send(b"restored deadline", Instant::now() + Duration::from_secs(1)).is_err());
    }
}

#[test]
fn foreign_final_selection_reply_poison_cannot_reconnect_or_retarget_the_same_stream() {
    let selection = ProgramSelection { key: crate::bootstrap_graph::query::tests::request().key,
        configured_targo: b"/output/private-child/bin/cargo".to_vec(),
        configured_compiler: b"/output/private-child/bin/trustc".to_vec() };
    let original = selection.clone();
    let mut reply = ProgramSelectionReply { selection: selection.clone(),
        namespace: b"/output/private-child".to_vec(), remaining_root_ns: 1_000_000_000 };
    reply.selection.configured_targo = b"/output/private-child/bin/targo".to_vec();
    let (client, server) = UnixStream::pair().unwrap();
    let deadline = Instant::now() + Duration::from_secs(3);
    let peer = thread::spawn(move || -> io::Result<()> {
        let mut channel = Channel::new(server)?;
        if ProgramSelection::decode(&channel.receive(deadline)?)? != original {
            return Err(crate::wire::invalid());
        }
        channel.send(&reply.encode()?, deadline)
    });
    let mut channel = Channel::new(client).unwrap();
    assert!(select(&mut channel, &selection, deadline).is_err());
    assert!(channel.poisoned());
    assert!(channel.send(b"different selector", deadline).is_err());
    peer.join().unwrap().unwrap();
}
