// Trust: Settlement-guard regressions live in a separate test file for tidy.
use rustc_span::def_id::{CRATE_DEF_ID, DefIndex};

use super::*;

#[test]
fn copied_generic_args_keep_the_interned_instance_identity() {
    let copies = [ty::GenericArgs::empty(); 2];
    // Distinct wrapper slots describe the same interned argument list.
    assert_ne!(std::ptr::from_ref(&copies[0]), std::ptr::from_ref(&copies[1]));
    let did = CRATE_DEF_ID.to_def_id();
    assert_eq!(instance_key(did, copies[0]), instance_key(did, copies[1]));
    let session = (7, 11);
    let mut state = InstanceWalkState { session, ..InstanceWalkState::default() };
    state.done.insert(instance_key(did, copies[0]), None);
    assert!(state.has_settled_no_edge(session, instance_key(did, copies[1])));
    assert!(!state.has_settled_no_edge((7, 12), instance_key(did, copies[1])));
}

#[test]
fn call_leaf_cannot_export_a_provisional_cycle_or_later_refusal() {
    let outer = (CRATE_DEF_ID.to_def_id(), 1);
    let inner = (DefId::local(DefIndex::from_u32(1)), 2);
    let session = (7, 11);
    let mut state = InstanceWalkState { session, ..InstanceWalkState::default() };
    state.in_progress.extend([outer, inner]);
    // The same-key recursive answer and a nested no-edge return both have
    // no completed entry. Neither may escape into the independent cache.
    assert!(!state.has_settled_no_edge(session, outer));
    assert!(!state.has_settled_no_edge(session, inner));
    state.in_progress.pop();
    assert!(!state.has_settled_no_edge(session, inner));
    state.in_progress.pop();
    state.done.insert(outer, Some("a dependency edge after the recursive branch".into()));
    assert!(!state.has_settled_no_edge(session, outer));
    assert!(!state.has_settled_no_edge(session, inner));
}

#[test]
fn call_leaf_reuses_only_the_settled_instance_in_the_same_session() {
    let key = (CRATE_DEF_ID.to_def_id(), 1);
    let other_args = (key.0, 2);
    let other_definition = (DefId::local(DefIndex::from_u32(1)), key.1);
    let session = (7, 11);
    let mut state = InstanceWalkState { session, ..InstanceWalkState::default() };
    state.done.insert(key, None);
    assert!(state.has_settled_no_edge(session, key));
    assert!(!state.has_settled_no_edge((8, 11), key));
    assert!(!state.has_settled_no_edge((7, 12), key));
    assert!(!state.has_settled_no_edge(session, other_args));
    assert!(!state.has_settled_no_edge(session, other_definition));
    // An unrelated active walk does not invalidate an already settled key.
    state.in_progress.push(other_args);
    assert!(state.has_settled_no_edge(session, key));
    assert!(!state.has_settled_no_edge(session, other_args));
}
