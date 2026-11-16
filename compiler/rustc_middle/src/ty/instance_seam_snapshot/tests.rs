// Trust: preserve the frozen production snapshot while separating test layout.
use super::*;

#[test]
fn duplicate_built_snapshot_is_permanently_poisoned() {
    let mut table = FxHashMap::default();
    trust_record_instance_seam_snapshot(&mut table, 1u32, || "first");
    assert_eq!(table.get(&1), Some(&Some("first")));
    trust_record_instance_seam_snapshot(&mut table, 2u32, || "other");
    for _ in 0..3 {
        trust_record_instance_seam_snapshot(&mut table, 1u32, || panic!("duplicate allocated"));
        assert_eq!(table.get(&1), Some(&None));
    }
    assert_eq!(table.get(&2), Some(&Some("other")));
    assert_eq!(table.get(&3), None);
}

#[test]
fn production_snapshot_bytes_match_the_frozen_pin() {
    let current = include_str!("../instance_seam_snapshot.rs");
    // Retain every byte before the test marker, including its preceding blank line.
    let (production, _) = current.split_once("#[cfg(test)]\n").unwrap();
    assert_eq!(production, include_str!("pinned-production.txt"));
}
