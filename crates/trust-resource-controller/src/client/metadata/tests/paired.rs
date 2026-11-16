use sha2::{Digest, Sha256};

use super::*;
use crate::paired_qualification::query::Completion;
use crate::paired_qualification::query::tests::query;

fn input(query: &crate::paired_qualification::query::CompilerQuery) -> MetadataPrepared {
    let mut value = prepared();
    value.root = query.invocation.consumer.root.clone();
    value.executable.path = query.invocation.consumer.compiler.path.clone();
    value.executable.sha256 = query.invocation.consumer.compiler.sha256;
    value
}
fn terminal(query: &crate::paired_qualification::query::CompilerQuery) -> Completion {
    let MetadataEvent::Completed(completed) = completed(Ok(())) else { unreachable!() };
    Completion {
        invocation_sha256: Sha256::digest(query.invocation.binding_preimage().unwrap()).into(),
        completed,
        observation: crate::accounting::Observation::uncollected(),
    }
}
fn send_start(
    peer: &mut Channel,
    query: &crate::paired_qualification::query::CompilerQuery,
    deadline: Instant,
) {
    for event in [
        status(Status::Attached),
        MetadataEvent::Prepared(input(query)),
        status(Status::Started(started())),
    ] {
        peer.send(&event.encode().unwrap(), deadline).unwrap();
    }
}

#[test]
fn paired_query_same_stream_owner_retains_output_exit_and_optional_accounting_until_eof() {
    let query = query();
    let request = NativeQueryRequest::Paired(query.clone());
    require_workload_observer(&request).unwrap();
    let (mut streams, peer, mut stdout, mut stderr) = actual_streams();
    let mut peer = Channel::new(peer).unwrap();
    let deadline = Instant::now() + Duration::from_secs(10);
    send_start(&mut peer, &query, deadline);
    let completion = terminal(&query);
    peer.send(&completion.encode().unwrap(), deadline).unwrap();
    stdout.write_all(b"actual paired stdout\0").unwrap();
    stderr.write_all(b"actual paired diagnostic\xff").unwrap();
    assert!(matches!(streams.poll(&request, deadline).unwrap(), StreamReady::Pending));
    assert!(streams.state.completed.is_some());
    assert!(streams.state.workload.is_none());
    drop((stdout, stderr, peer));
    loop {
        match streams.poll(&request, deadline).unwrap() {
            StreamReady::Completed => break,
            StreamReady::Pending if Instant::now() < deadline => {
                std::thread::sleep(Duration::from_millis(1))
            }
            _ => panic!("paired owner did not observe original stream retirement"),
        }
    }
    assert_eq!(streams.output.bytes[0], b"actual paired stdout\0");
    assert_eq!(streams.output.bytes[1], b"actual paired diagnostic\xff");
    assert_eq!(streams.state.paired.as_ref(), Some(&completion));
    assert_eq!(streams.state.accounting, Some(crate::accounting::Observation::uncollected()));
    assert!(matches!(
        streams.state.completed.as_ref().unwrap().finished.status,
        Status::Finished { outcome: Outcome::Exit(7), .. }
    ));
}

#[test]
fn paired_query_rejects_generic_v1_foreign_and_replayed_retirement_without_fallback() {
    for mutation in 0..6 {
        let query = query();
        let request = NativeQueryRequest::Paired(query.clone());
        let (mut streams, peer, stdout, stderr) = actual_streams();
        let mut peer = Channel::new(peer).unwrap();
        let deadline = Instant::now() + Duration::from_secs(10);
        send_start(&mut peer, &query, deadline);
        let mut completion = terminal(&query);
        let bytes = match mutation {
            0 => completion.completed.encode().unwrap(),
            1 => crate::workload::host::Completion {
                phase: 0,
                kind: crate::workload::host::MemberKind::CompilerQuery,
                completed: completion.completed.clone(),
                observation: completion.observation,
            }
            .encode()
            .unwrap(),
            2 => {
                completion.invocation_sha256[0] ^= 1;
                completion.encode().unwrap()
            }
            3 => {
                completion.completed.finished.member_attempt[0] ^= 1;
                completion.encode().unwrap()
            }
            4 => {
                peer.send(&completion.encode().unwrap(), deadline).unwrap();
                completion.encode().unwrap()
            }
            5 => {
                let mut changed = query.invocation.clone();
                changed.ay.cargo_config.sha256[0] ^= 1;
                completion.invocation_sha256 =
                    Sha256::digest(changed.binding_preimage().unwrap()).into();
                completion.encode().unwrap()
            }
            _ => unreachable!(),
        };
        peer.send(&bytes, deadline).unwrap();
        drop((peer, stdout, stderr));
        assert!(streams.poll(&request, deadline).is_err(), "mutation {mutation}");
        assert!(streams.failed);
        assert!(streams.poll(&request, deadline).is_err(), "failure is sticky");
        assert!(streams.state.workload.is_none());
    }
}

#[test]
fn paired_preparation_rejects_changed_original_compiler_plan_or_attempt() {
    let query = query();
    let original = input(&query);
    query.validate_prepared(&original).unwrap();
    for mutation in 0..5 {
        let mut changed = original.clone();
        match mutation {
            0 => changed.executable.sha256[0] ^= 1,
            1 => changed.executable.path = b"/sdk/bin/foreign".to_vec(),
            2 => changed.root = b"/foreign".to_vec(),
            3 => changed.root_attempt[0] ^= 1,
            4 => changed.member_attempt[0] ^= 1,
            _ => unreachable!(),
        }
        assert!(query.validate_prepared(&changed).is_err());
    }
}
