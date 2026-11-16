use super::*;

pub(crate) fn request() -> Request {
    Request {
        key: Key { root_attempt: [1; 16], invocation_sha256: [2; 32], attempt: [3; 16] },
        output_root: b"/outputs".to_vec(),
        locks: [".cargo-lock", ".cargo-build-lock", ".cargo-artifact-lock"]
            .iter()
            .enumerate()
            .map(|(n, name)| Lock {
                path: format!("/outputs/debug/{name}").into_bytes(),
                backing: FileIdentity { device: 1, inode: n as u64 + 1 },
            })
            .collect(),
    }
}
#[test]
fn complete_original_set_and_key_are_exact_without_a_guard_constructor() {
    let request = request();
    assert_eq!(Request::decode(&request.encode().unwrap()).unwrap(), request);
    let retained = Reply::Retained { key: request.key.clone(), locks: request.locks.clone() };
    assert_eq!(Reply::decode(&retained.encode().unwrap(), &request).unwrap(), retained);
    let refused = Reply::Refused {
        key: request.key.clone(),
        reason: "actual original guard handoff refused".into(),
    };
    assert_eq!(Reply::decode(&refused.encode().unwrap(), &request).unwrap(), refused);
    let mut changed = request.clone();
    changed.key.attempt = [4; 16];
    assert!(Reply::decode(&retained.encode().unwrap(), &changed).is_err());
    for changed in 0..3 {
        let mut locks = request.locks.clone();
        match changed {
            0 => {
                locks.pop();
            }
            1 => locks.swap(0, 1),
            _ => locks[0].backing.inode += 10,
        };
        let reply = Reply::Retained { key: request.key.clone(), locks };
        assert!(Reply::decode(&reply.encode().unwrap(), &request).is_err());
    }
}
#[test]
fn guard_paths_population_aliases_and_versions_refuse_without_truncation() {
    let request = request();
    for changed in 0..6 {
        let mut bad = request.clone();
        match changed {
            0 => bad.locks.clear(),
            1 => bad.locks = vec![bad.locks[0].clone(); MAX_LOCKS + 1],
            2 => bad.locks[0].path = b"/outputs-other/.cargo-lock".to_vec(),
            3 => bad.locks[0].path = b"/outputs/debug/../.cargo-lock".to_vec(),
            4 => bad.locks[0].path = b"/outputs/debug/arbitrary".to_vec(),
            _ => bad.locks[1].backing = bad.locks[0].backing,
        }
        assert!(bad.encode().is_err(), "changed{changed}");
    }
    let mut bytes = request.encode().unwrap();
    bytes[16..24].copy_from_slice(&1u64.to_be_bytes());
    assert!(Request::decode(&bytes).is_err(), "program registration is a different profile");
    let mut bytes = request.encode().unwrap();
    bytes.extend(0u64.to_be_bytes());
    assert!(Request::decode(&bytes).is_err());
}
#[test]
fn warm_selection_binds_complete_original_receipt_and_one_use_sequence() {
    let selected=Selection {retained:request(),sequence:1,attempt:[4;16]};
    let bytes=selected.encode().unwrap();assert_eq!(Selection::decode(&bytes).unwrap(),selected);
    for end in 0..bytes.len() {assert!(Selection::decode(&bytes[..end]).is_err());}
    let reply=SelectionReply {selection:selected.clone(),decision:SelectionDecision::Selected}.encode().unwrap();
    assert!(SelectionReply::decode(&reply,&selected).is_ok());
    for changed in 0..5 {
        let mut other=selected.clone();
        match changed {0=>other.sequence+=1,1=>other.attempt=[5;16],2=>other.retained.key.attempt=[6;16],3=>other.retained.locks.swap(0,1),_=>other.retained.locks[0].backing.inode+=10};
        assert!(SelectionReply::decode(&reply,&other).is_err(),"selection change {changed}");
    }
    let mut zero=selected.clone();zero.sequence=0;assert!(zero.encode().is_err());
    let mut replay=selected;replay.attempt=replay.retained.key.attempt;assert!(replay.encode().is_err());
}
