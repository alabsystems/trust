//! `MemberKeyScope`: every answer is the unchanged computation's, each registered element's key
//! is computed at most once, and nothing outside a live scope's own storage is answered.

use super::super::bundled_member_source_identity_key;
use super::*;

/// A minimal member: `def_path` and the span line make the content (and so the key) distinct.
fn member(def_path: &str, line: u32) -> trust_types::VerifiableFunction {
    trust_types::VerifiableFunction {
        name: def_path.rsplit("::").next().unwrap_or(def_path).to_string(),
        def_path: def_path.to_string(),
        span: trust_types::SourceSpan {
            file: "member_source_identity_scope.rs".to_string(),
            line_start: line,
            col_start: 1,
            line_end: line + 2,
            col_end: 2,
        },
        body: trust_types::VerifiableBody {
            locals: vec![trust_types::LocalDecl {
                index: 0,
                ty: trust_types::Ty::Int { width: 32, signed: false },
                name: None,
            }],
            blocks: vec![trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: Vec::new(),
                terminator: trust_types::Terminator::Return,
            }],
            arg_count: 0,
            return_ty: trust_types::Ty::Int { width: 32, signed: false },
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn members() -> Vec<trust_types::VerifiableFunction> {
    vec![
        member("scope::root", 1),
        member("scope::callee", 10),
        member("core::ops::index", 20),
        // The SAME content as `scope::callee`, in other storage: equal key, separate element.
        member("scope::callee", 10),
    ]
}

/// What the code before scopes returned: the key over the UNMEMOIZED digest.
fn old_key(member: &trust_types::VerifiableFunction) -> BundledMemberSourceIdentityKey {
    BundledMemberSourceIdentityKey {
        name: member.name.clone(),
        def_path: member.def_path.clone(),
        source_digest: compiler_function_source_digest_hex(member).expect("serializes"),
    }
}

#[test]
fn scoped_keys_are_the_old_keys_and_each_is_computed_once() {
    let members = members();
    let scope = MemberKeyScope::new(&members);
    assert_eq!(scope.counts(), (0, 0), "registration computes nothing");
    for _ in 0..5 {
        for member in &members {
            assert_eq!(bundled_member_source_identity_key(member).expect("key"), old_key(member));
        }
    }
    assert_eq!(scope.counts(), (5 * members.len(), members.len()), "asked 5x, computed 1x each");
    assert_eq!(
        bundled_member_source_identity_key(&members[1]).expect("key"),
        bundled_member_source_identity_key(&members[3]).expect("key"),
        "equal content in separate storage: separate entries, the same key"
    );
}

#[test]
fn a_clone_or_an_unregistered_member_is_computed_not_answered() {
    let members = members();
    let scope = MemberKeyScope::new(&members);
    let clone = members[2].clone();
    assert!(scoped_key(&clone).is_none(), "a clone lives in other storage");
    assert_eq!(bundled_member_source_identity_key(&clone).expect("key"), old_key(&clone));
    let unregistered = member("scope::elsewhere", 30);
    assert!(scoped_key(&unregistered).is_none());
    assert_eq!(
        bundled_member_source_identity_key(&unregistered).expect("key"),
        old_key(&unregistered)
    );
    assert_eq!(scope.counts(), (0, 0), "neither was answered from the table");
}

#[test]
fn a_dropped_scope_answers_nothing_and_a_changed_member_gets_its_new_key() {
    let mut members = members();
    let scope = MemberKeyScope::new(&members);
    let before = bundled_member_source_identity_key(&members[0]).expect("key");
    assert_eq!(scope.counts(), (1, 1));
    drop(scope);
    assert!(scoped_key(&members[0]).is_none(), "no table survives its guard");
    // Only now, with no borrow left, can the member change; its key is the new content's.
    members[0].span.line_end += 1;
    let after = bundled_member_source_identity_key(&members[0]).expect("key");
    assert_ne!(after, before, "a changed member must never be answered its old key");
    assert_eq!(after, old_key(&members[0]));
}

#[test]
fn nested_scopes_answer_from_their_own_storage_and_drop_in_any_order() {
    let outer_members = members();
    let inner_members = vec![member("scope::nested", 40), member("scope::nested_callee", 50)];
    let outer = MemberKeyScope::new(&outer_members);
    let inner = MemberKeyScope::new(&inner_members);
    assert_eq!(
        bundled_member_source_identity_key(&outer_members[2]).expect("key"),
        old_key(&outer_members[2])
    );
    assert_eq!(
        bundled_member_source_identity_key(&inner_members[1]).expect("key"),
        old_key(&inner_members[1])
    );
    assert_eq!(outer.counts(), (1, 1));
    assert_eq!(inner.counts(), (1, 1));
    // The enclosing scope ends first: the nested one still answers, the enclosing one not.
    drop(outer);
    assert!(scoped_key(&outer_members[2]).is_none());
    assert_eq!(
        bundled_member_source_identity_key(&inner_members[1]).expect("key"),
        old_key(&inner_members[1])
    );
    assert_eq!(inner.counts(), (2, 1));
    drop(inner);
    assert!(scoped_key(&inner_members[1]).is_none());
}

#[test]
fn a_subslice_scope_and_its_parent_scope_agree() {
    let members = members();
    let whole = MemberKeyScope::new(&members);
    let tail = MemberKeyScope::new(&members[1..]);
    // The innermost table holding the element answers; both would compute the same key.
    assert_eq!(bundled_member_source_identity_key(&members[2]).expect("key"), old_key(&members[2]));
    assert_eq!(tail.counts(), (1, 1));
    assert_eq!(whole.counts(), (0, 0));
    // An element only the parent holds is answered by the parent.
    assert_eq!(bundled_member_source_identity_key(&members[0]).expect("key"), old_key(&members[0]));
    assert_eq!(whole.counts(), (1, 1));
    drop(tail);
    assert_eq!(bundled_member_source_identity_key(&members[2]).expect("key"), old_key(&members[2]));
    assert_eq!(whole.counts(), (2, 2));
}

/// A subslice scope that ENDS before its parent does: the element just past its end belongs to
/// the parent alone. Without the `index < len` bound in `Table::index_of` the subslice's table
/// would claim it and index past its own keys (review plant 6, which the tests above missed).
#[test]
fn a_subslice_scope_does_not_claim_the_element_after_its_end() {
    let members: Vec<_> = (0..5).map(|i| member(&format!("scope::m{i}"), 10 * i + 1)).collect();
    let whole = MemberKeyScope::new(&members);
    let middle = MemberKeyScope::new(&members[1..2]);
    for member in &members {
        assert_eq!(bundled_member_source_identity_key(member).expect("key"), old_key(member));
    }
    assert_eq!(middle.counts(), (1, 1), "only members[1] is the middle scope's");
    assert_eq!(whole.counts(), (4, 4), "every other element is the parent's");
}

/// One path, three contents, all in one live scope (generic instances and re-extractions share a
/// `def_path`): each element is answered its OWN content's key, never a sibling's.
#[test]
fn members_sharing_a_path_are_answered_their_own_keys() {
    let mut members =
        vec![member("scope::same", 1), member("scope::same", 4), member("scope::same", 1)];
    members[2].span.col_end += 1;
    let scope = MemberKeyScope::new(&members);
    for _ in 0..3 {
        for member in &members {
            assert_eq!(bundled_member_source_identity_key(member).expect("key"), old_key(member));
        }
    }
    let digests: Vec<String> = members.iter().map(|member| old_key(member).source_digest).collect();
    assert!(digests[0] != digests[1] && digests[1] != digests[2] && digests[0] != digests[2]);
    assert_eq!(scope.counts(), (9, 3));
}

/// The audit that proved the scoped answers equal the old ones must itself flag a wrong answer
/// (review plant 7: a comparison that always said "matches" passed every test above).
#[test]
fn the_audit_flags_every_wrong_answer() {
    let members = members();
    let changed = {
        let mut changed = members[0].clone();
        changed.span.line_end += 1;
        changed
    };
    let old = old_computation(&members[0]);
    assert_eq!(old.clone().expect("serializes"), old_key(&members[0]), "the old computation");
    assert!(same_answer(&Ok(old_key(&members[0])), &old), "the right answer matches");
    assert!(!same_answer(&Ok(old_key(&members[1])), &old), "another member's key");
    assert!(!same_answer(&Ok(old_key(&changed)), &old), "same name and path, other content");
    assert!(!same_answer(&Err("no key".to_string()), &old), "an error for a key");
    assert!(!same_answer(&old, &Err("no key".to_string())), "a key for an error");
    assert!(same_answer(&Err("a".to_string()), &Err("b".to_string())), "both errors");
}

#[test]
fn an_empty_scope_answers_nothing() {
    let none: Vec<trust_types::VerifiableFunction> = Vec::new();
    let scope = MemberKeyScope::new(&none);
    let unregistered = member("scope::alone", 60);
    assert!(scoped_key(&unregistered).is_none());
    assert_eq!(scope.counts(), (0, 0));
}
