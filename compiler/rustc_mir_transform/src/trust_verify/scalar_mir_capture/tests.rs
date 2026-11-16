use super::bounded_debug;

#[test]
fn scalar_body_capture_retention_never_returns_a_truncated_success() {
    assert_eq!(bounded_debug(&[1_u8, 2]).unwrap(), "[\n    1,\n    2,\n]");
    assert!(bounded_debug(&"x".repeat(1024 * 1024)).is_err());
    // Debug escaping can exceed the bound even when the input string
    // itself is smaller; count bytes actually written, not source chars.
    assert!(bounded_debug(&"\n".repeat(600_000)).is_err());
}
