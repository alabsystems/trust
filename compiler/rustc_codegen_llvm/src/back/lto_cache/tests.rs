use super::cache_keys_match;

#[test]
fn unavailable_or_different_keys_never_reuse() {
    for (previous, current) in [
        (None, None),
        (Some("key"), None),
        (None, Some("key")),
        (Some("old"), Some("new")),
        (Some(""), Some("")),
    ] {
        assert!(!cache_keys_match(previous, current), "{previous:?}, {current:?}");
    }
}

#[test]
fn matching_available_keys_allow_reuse() {
    assert!(cache_keys_match(Some("key"), Some("key")));
}
