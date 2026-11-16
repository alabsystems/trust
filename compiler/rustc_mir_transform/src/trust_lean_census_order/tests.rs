use super::CheckPhase::*;
use super::*;

fn inventory() -> IslandCheckOrder {
    let mut order = IslandCheckOrder::default();
    order.inventory(vec![(10, 20), (30, 40), (50, 60)]).unwrap();
    order
}

/// The deferred suffix's phase in the lane that actually ran.
fn suffix_phase(verification: bool) -> CheckPhase {
    if verification { AfterProgramAdmissions } else { VerificationDisabled }
}

fn checked(order: &IslandCheckOrder) -> Vec<usize> {
    order.checked.iter().copied().collect()
}

#[test]
fn header_batch_then_admissions_then_one_import_batch_suffix() {
    for verification in [false, true] {
        let mut order = inventory();
        assert_eq!(order.check(&[(10, 20)], HeaderFirst, verification, false).unwrap(), [0]);
        order.admissions_boundary().unwrap();
        let suffix =
            order.check(&[(30, 40), (50, 60)], suffix_phase(verification), verification, false);
        assert_eq!(suffix.unwrap(), [1, 2]);
        assert_eq!(order.completion_count(), Ok(3));
    }
}

#[test]
fn the_suffix_is_one_batch_after_the_boundary_in_its_own_lane() {
    for verification in [false, true] {
        let phase = suffix_phase(verification);
        let mut order = inventory();
        order.check(&[(10, 20)], HeaderFirst, verification, false).unwrap();
        // Before the boundary the minted admissions do not exist yet.
        assert!(order.check(&[(30, 40)], phase, verification, false).is_err());
        order.admissions_boundary().unwrap();
        // The other lane's phase names a lane that did not run.
        assert!(
            order.check(&[(30, 40)], suffix_phase(!verification), verification, false).is_err()
        );
        order.check(&[(30, 40)], phase, verification, false).unwrap();
        // A second suffix batch, even over a later island, is not TG14's
        // single import batch; nor is a header batch after the suffix.
        assert!(order.check(&[(50, 60)], phase, verification, false).is_err());
        assert!(order.check(&[(50, 60)], HeaderFirst, verification, false).is_err());
        assert_eq!(checked(&order), [0, 1]);
        assert!(order.completion_count().is_err());
    }
}

#[test]
fn all_deferred_and_empty_crates_record_the_boundary_in_both_lanes() {
    for verification in [false, true] {
        let mut order = inventory();
        order.admissions_boundary().unwrap();
        let all = [(10, 20), (30, 40), (50, 60)];
        let suffix = order.check(&all, suffix_phase(verification), verification, false);
        assert_eq!(suffix.unwrap(), [0, 1, 2]);
        assert_eq!(order.completion_count(), Ok(3));
        let mut empty = IslandCheckOrder::default();
        empty.inventory(Vec::new()).unwrap();
        // Both lanes reach the admission mint before completion.
        assert!(empty.completion_count().is_err());
        empty.admissions_boundary().unwrap();
        assert_eq!(empty.completion_count(), Ok(0));
    }
}

#[test]
fn missing_and_duplicate_inventory_and_admission_transitions_are_refused() {
    let mut order = IslandCheckOrder::default();
    assert!(order.check(&[(10, 20)], HeaderFirst, true, false).is_err());
    assert!(order.admissions_boundary().is_err());
    assert!(order.completion_count().is_err());
    order.inventory(vec![(10, 20)]).unwrap();
    assert!(order.inventory(Vec::new()).is_err());
    order.admissions_boundary().unwrap();
    assert!(order.admissions_boundary().is_err());
    assert!(order.check(&[(10, 20)], HeaderFirst, true, false).is_err());
    assert!(order.check(&[(10, 20)], VerificationDisabled, true, false).is_err());
    assert!(order.check(&[(10, 20)], AfterProgramAdmissions, false, false).is_err());
    order.check(&[(10, 20)], AfterProgramAdmissions, true, false).unwrap();
    // A boundary after the suffix would split a batch that ran once.
    assert!(order.admissions_boundary().is_err());
    assert_eq!(order.completion_count(), Ok(1));
}

#[test]
fn invalid_phases_and_cardinalities_do_not_consume_islands() {
    let mut order = inventory();
    assert!(order.check(&[], HeaderFirst, true, false).is_err());
    assert!(order.check(&[(10, 20)], AfterProgramAdmissions, true, false).is_err());
    assert!(order.check(&[(10, 20)], VerificationDisabled, false, false).is_err());
    assert!(order.check(&[(10, 20)], VerificationDisabled, true, false).is_err());
    assert!(order.checked.is_empty());
    order.check(&[(10, 20), (30, 40)], HeaderFirst, false, false).unwrap();
    assert!(order.check(&[(50, 60)], HeaderFirst, false, false).is_err());
    order.admissions_boundary().unwrap();
    assert!(order.check(&[], VerificationDisabled, false, false).is_err());
    assert!(order.check(&[(50, 60)], AfterProgramAdmissions, false, false).is_err());
    assert_eq!(checked(&order), [0, 1]);
    order.check(&[(50, 60)], VerificationDisabled, false, false).unwrap();
    assert_eq!(order.completion_count(), Ok(3));
}

#[test]
fn missing_duplicate_ambiguous_and_reordered_identities_are_refused_atomically() {
    for positions in [vec![(10, 20), (10, 20)], vec![(30, 40), (10, 20)], vec![(99, 100)]] {
        let mut order = inventory();
        assert!(order.check(&positions, HeaderFirst, false, false).is_err());
        assert!(order.checked.is_empty());
        order.check(&[(10, 20), (30, 40), (50, 60)], HeaderFirst, false, false).unwrap();
        order.admissions_boundary().unwrap();
        assert_eq!(order.completion_count(), Ok(3));
    }
    // The suffix batch is just as atomic: a refused batch consumes nothing
    // and does not use up the lane's one suffix.
    for positions in [vec![(30, 40), (30, 40)], vec![(50, 60), (30, 40)], vec![(30, 40), (99, 100)]]
    {
        let mut order = inventory();
        order.check(&[(10, 20)], HeaderFirst, true, false).unwrap();
        order.admissions_boundary().unwrap();
        assert!(order.check(&positions, AfterProgramAdmissions, true, false).is_err());
        assert_eq!(checked(&order), [0]);
        order.check(&[(30, 40), (50, 60)], AfterProgramAdmissions, true, false).unwrap();
        assert_eq!(order.completion_count(), Ok(3));
    }
    let mut ambiguous = IslandCheckOrder::default();
    ambiguous.inventory(vec![(10, 20), (10, 20)]).unwrap();
    assert!(ambiguous.check(&[(10, 20)], HeaderFirst, false, false).is_err());
    ambiguous.admissions_boundary().unwrap();
    assert!(ambiguous.completion_count().is_err());
}

#[test]
fn failed_source_recovery_keeps_later_checks_but_cannot_complete() {
    for verification in [false, true] {
        let phase = suffix_phase(verification);
        let mut order = inventory();
        assert_eq!(order.check(&[(30, 40)], HeaderFirst, verification, false).unwrap(), [1]);
        order.admissions_boundary().unwrap();
        // Island 0 precedes the checked island 1: out of source order.
        assert!(order.check(&[(10, 20), (50, 60)], phase, verification, false).is_err());
        assert_eq!(checked(&order), [1]);
        assert_eq!(order.check(&[(50, 60)], phase, verification, false).unwrap(), [2]);
        assert_eq!(checked(&order), [1, 2]);
        assert!(order.completion_count().is_err());
    }
}

#[test]
fn rejected_prefix_and_suffix_batches_are_retained_without_success_footer() {
    for verification in [false, true] {
        let phase = suffix_phase(verification);
        // TG14 names a refused unit and commits the rest; the batch is still
        // a rejected language check.
        let mut suffix = inventory();
        suffix.check(&[(10, 20)], HeaderFirst, verification, false).unwrap();
        suffix.admissions_boundary().unwrap();
        suffix.check(&[(30, 40), (50, 60)], phase, verification, true).unwrap();
        assert_eq!(suffix.checked.len(), 3);
        assert!(suffix.rejected);
        assert!(suffix.completion_count().is_err());
        // An accepted suffix does not clear an earlier rejected prefix.
        let mut prefix = inventory();
        prefix.check(&[(10, 20)], HeaderFirst, verification, true).unwrap();
        prefix.admissions_boundary().unwrap();
        prefix.check(&[(30, 40), (50, 60)], phase, verification, false).unwrap();
        assert_eq!(prefix.checked.len(), 3);
        assert!(prefix.completion_count().is_err());
    }
}
