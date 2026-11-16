// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! Strict framing only; these DATA fixtures create no native inputs or grants.
use super::*;
fn request() -> ScopeRequest {
    ScopeRequest {
        query: ContextQuery {
            binding: crate::JobBinding {
                session: "s-ab12".into(),
                root_attempt: [1; 16],
                capability: [2; 32],
            },
            call_attempt: [3; 16],
        },
        coordinator: [4; 16],
        member: [5; 16],
        directory: b"/selected/private/unit".to_vec(),
        files: vec![ScopeFile {
            path: b"/selected/retired.rmeta".to_vec(),
            producer: [6; 16],
        }],
    }
}
#[test]
fn original_attachment_framing_is_complete_bounded_and_attempt_specific() {
    let original = request();
    let bytes = original.encode().unwrap();
    assert!(ScopeRequest::decode(&bytes).unwrap() == original);
    for end in 0..bytes.len() {
        assert!(ScopeRequest::decode(&bytes[..end]).is_err());
    }
    let mut extra = bytes;
    extra.push(0);
    assert!(ScopeRequest::decode(&extra).is_err());
    let reply = ScopeReply {
        member: original.member,
    }
    .encode()
    .unwrap();
    ScopeReply::decode(&reply, &original).unwrap();
    let mut other = original.clone();
    other.member = [7; 16];
    assert!(ScopeReply::decode(&reply, &other).is_err());
    for variant in 0..5 {
        let mut bad = original.clone();
        match variant {
            0 => bad.files.push(bad.files[0].clone()),
            1 => bad.files[0].producer = bad.member,
            2 => bad.directory = b"relative".to_vec(),
            3 => bad.files[0].path.push(0),
            4 => bad.files = vec![bad.files[0].clone(); MAX_SCOPE_FILES + 1],
            _ => unreachable!(),
        }
        assert!(bad.encode().is_err());
    }
    assert!(super::super::CompilerSelection::decode(&reply).is_err());
}
