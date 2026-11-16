// Trust: exercise generated iteration, checked and overflowing Step boundaries.
use std::iter::Step;

use crate as rustc_index;

crate::newtype_index! {
    #[orderable]
    struct StepIndex {}
}

#[test]
fn newtype_step_preserves_ranges_and_checked_boundaries() {
    let low = StepIndex::from_usize(1);
    let high = StepIndex::from_usize(4);
    assert_eq!(Step::steps_between(&low, &high), (3, Some(3)));
    assert_eq!((low..high).map(StepIndex::as_usize).collect::<Vec<_>>(), [1, 2, 3]);
    assert_eq!((low..high).rev().map(StepIndex::as_usize).collect::<Vec<_>>(), [3, 2, 1]);
    assert_eq!(Step::forward_checked(low, 2), Some(StepIndex::from_usize(3)));
    assert_eq!(Step::forward_checked(low, usize::MAX), None);
    assert_eq!(Step::backward_checked(StepIndex::from_usize(0), 1), None);
    assert_eq!(Step::forward_overflowing(low, usize::MAX), (StepIndex::from_usize(0), true));
    assert_eq!(
        Step::backward_overflowing(StepIndex::from_usize(0), usize::MAX),
        (StepIndex::from_usize(1), true)
    );
}
