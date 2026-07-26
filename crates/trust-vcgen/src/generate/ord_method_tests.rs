use super::ord_method;

#[test]
fn matches_std_ord_min_max_clamp() {
    // The spellings safe_def_path_str produces for `n.min(3)` etc.
    assert_eq!(ord_method("std::cmp::Ord::min"), Some("min"));
    assert_eq!(ord_method("core::cmp::Ord::max"), Some("max"));
    assert_eq!(ord_method("std::cmp::Ord::clamp"), Some("clamp"));
    assert_eq!(ord_method("<usize as Ord>::min"), Some("min"));
    assert_eq!(ord_method("core::cmp::min"), Some("min"));
}

#[test]
fn rejects_comparator_variants_unsound_to_bound() {
    // min_by / min_by_key take a comparator; `result <= a` does NOT hold.
    assert_eq!(ord_method("std::cmp::Ord::min_by"), None);
    assert_eq!(ord_method("core::cmp::min_by_key"), None);
    // `Iterator::min` returns the min ELEMENT (Option<&T>), not a 2-arg
    // Ord::min — outside `cmp`/`Ord`, so (correctly) not bounded.
    assert_eq!(ord_method("std::iter::Iterator::min"), None);
}

#[test]
fn rejects_user_min_outside_std_cmp() {
    // A user `mymod::min` is NOT the ordered min — must not be bounded.
    assert_eq!(ord_method("mycrate::mymod::min"), None);
    assert_eq!(ord_method("widget::clamp"), None);
}
