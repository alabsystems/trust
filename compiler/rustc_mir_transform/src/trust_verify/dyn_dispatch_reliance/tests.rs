// Trust (P-UB, absent UB-check members, 2026-11-08): the selection rule of
// `absent_ub_check_callee_keys`, which decides which absent-callee markers the
// writer-relative bar may excuse. Every case but the first must excuse NOTHING
// it is not entitled to.

use rustc_data_structures::fx::FxHashSet;

use super::absent_ub_check_callee_keys;

const ADD: &str = "core::ptr::mut_ptr::<impl *mut T>::add::precondition_check";

fn keys(names: &[&str]) -> FxHashSet<String> {
    names.iter().map(|name| name.to_string()).collect()
}

#[test]
fn an_absent_check_called_only_as_a_check_is_selected() {
    let candidates = [(1u32, ADD.to_string()), (1u32, ADD.to_string())];
    let selected =
        absent_ub_check_callee_keys(&candidates, &FxHashSet::default(), &keys(&[]), false);
    assert_eq!(selected, keys(&[ADD]));
}

#[test]
fn a_walked_check_mints_no_marker_and_is_not_selected() {
    let candidates = [(1u32, ADD.to_string())];
    let observed: FxHashSet<u32> = [1u32].into_iter().collect();
    assert!(absent_ub_check_callee_keys(&candidates, &observed, &keys(&[]), false).is_empty());
}

#[test]
fn a_key_any_other_call_renders_is_disqualified() {
    // Another callee (or a non-sysroot caller, a tail call, an indirect call)
    // rendered the same key: the marker could be that call's.
    let candidates = [(1u32, ADD.to_string())];
    let selected =
        absent_ub_check_callee_keys(&candidates, &FxHashSet::default(), &keys(&[ADD]), false);
    assert!(selected.is_empty());
}

#[test]
fn the_p_ub_belt_selects_nothing() {
    let candidates = [(1u32, ADD.to_string())];
    let selected =
        absent_ub_check_callee_keys(&candidates, &FxHashSet::default(), &keys(&[]), true);
    assert!(selected.is_empty());
}

#[test]
fn a_non_candidate_key_is_never_selected() {
    // Only candidates' keys can come out: an other-callee key alone yields none.
    let selected = absent_ub_check_callee_keys::<u32>(
        &[],
        &FxHashSet::default(),
        &keys(&["core::option::unwrap_failed"]),
        false,
    );
    assert!(selected.is_empty());
}
