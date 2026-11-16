use super::*;

#[test]
fn a_nested_failed_body_withholds_original_outer_acceptance() {
    let mut errors = PlannedOriginalErrors::default();
    let outer_entry = errors.count;
    errors.record(); // Original nested-body failure, not a chosen report.
    assert!(!errors.unchanged(outer_entry));
}

#[test]
fn an_older_failed_sibling_is_not_misattributed_to_a_safe_body() {
    let mut errors = PlannedOriginalErrors::default();
    errors.record();
    let safe_entry = errors.count;
    assert!(errors.unchanged(safe_entry));
    errors.record(); // A newer failure changes only a still-open baseline.
    assert!(!errors.unchanged(safe_entry));
}

#[test]
fn counter_exhaustion_never_becomes_an_unchanged_success() {
    let mut errors = PlannedOriginalErrors { count: u64::MAX, poisoned: false };
    errors.record();
    assert!(!errors.unchanged(u64::MAX));
}
