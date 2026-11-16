//! Selector DATA tests, without constructing an admitted Host or source owner.
use super::*;

pub(crate) fn intent() -> Intent {
    let request = super::super::tests::request();
    Intent {
        key: request.key,
        selection: crate::bootstrap_graph::offline_preparation::IntentSelection {
            source_root: request.source_root,
            output_root: request.output_root,
            configured_targo: request.configured_targo,
            configured_compiler: request.configured_compiler,
            environment: request.environment,
            budget_ns: request.budget_ns,
        },
    }
}
#[test]
fn intent_preserves_raw_environment_spelling_and_only_its_own_graph() {
    let intent = intent();
    let selection_bytes = intent.selection.encode().unwrap();
    assert!(IntentSelection::decode(&selection_bytes).unwrap() == intent.selection);
    assert!(IntentQuery::decode(&selection_bytes).is_err());
    assert!(Request::decode(&selection_bytes).is_err());
    for end in 0..selection_bytes.len() {
        assert!(IntentSelection::decode(&selection_bytes[..end]).is_err());
    }
    let mut trailing_selection = selection_bytes;
    trailing_selection.push(0);
    assert!(IntentSelection::decode(&trailing_selection).is_err());
    let query = IntentQuery { key: intent.key.graph.clone() };
    let reply = IntentReply { query: query.clone(), intent, remaining_root_ns: MAX_BUDGET_NS };
    let bytes = reply.encode().unwrap();
    assert!(IntentReply::decode(&bytes, &query).unwrap() == reply);
    assert!(IntentQuery::decode(&query.encode().unwrap()).unwrap() == query);
    assert!(
        query
            .hello()
            .unwrap()
            .windows(INTENT_PURPOSE.len())
            .any(|bytes| bytes == INTENT_PURPOSE.as_bytes())
    );
    assert!(
        reply.intent.selection.environment.contains(&(b"TARGO_BUILD_WARNINGS".to_vec(), vec![]))
    );
    assert!(
        reply.intent.selection.environment.contains(&(b"CALLER_OS_BYTES".to_vec(), vec![255, 254]))
    );
    let mut foreign = query;
    foreign.key.graph[0] ^= 1;
    assert!(IntentReply::decode(&bytes, &foreign).is_err());
    assert!(Request::decode(&bytes).is_err());
    assert!(IntentQuery::decode(&bytes).is_err());
    let mut trailing = bytes;
    trailing.push(0);
    assert!(IntentReply::decode(&trailing, &reply.query).is_err());
}
#[test]
fn intent_refuses_unbounded_policy_or_ambiguous_selectors() {
    let original = intent();
    for budget in [0, MAX_BUDGET_NS + 1, u64::MAX] {
        let mut bad = original.clone();
        bad.selection.budget_ns = budget;
        assert!(bad.validate().is_err());
    }
    for path in [b"relative".as_slice(), b"/source/../other", b"/source//other", b"/source\0"] {
        let mut bad = original.clone();
        bad.selection.configured_targo = path.to_vec();
        assert!(bad.validate().is_err());
    }
    let mut bad = original.clone();
    bad.selection.output_root = bad.selection.source_root.clone();
    assert!(bad.validate().is_err());
    let mut bad = original.clone();
    bad.key.sequence = 2;
    assert!(bad.validate().is_err());
    let mut bad = original.clone();
    bad.selection.environment.push(bad.selection.environment[0].clone());
    assert!(bad.validate().is_err());
    let mut bad = original;
    bad.selection.environment.retain(|(name, _)| name != b"CARGO_NET_OFFLINE");
    assert!(bad.validate().is_err());
}
#[test]
fn final_request_cannot_retarget_the_retained_initial_intent() {
    let intent = intent();
    let mut request = super::super::tests::request();
    intent.matches_request(&request).unwrap();
    request.budget_ns -= 1;
    intent.matches_request(&request).unwrap();
    request.configured_targo.push(b'x');
    assert!(intent.matches_request(&request).is_err());
    let mut request = super::super::tests::request();
    request.environment.retain(|(name, _)| name != b"TARGO_BUILD_WARNINGS");
    assert!(intent.matches_request(&request).is_err());
    let mut request = super::super::tests::request();
    request.key.operation[0] ^= 1;
    assert!(intent.matches_request(&request).is_err());
}
