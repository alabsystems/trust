use super::*;

#[test]
fn typed_policy_retains_both_independent_dimensions() {
    let policy = parse(r#"{"version":1,"inactivity_ms":25,"resident_bytes":4096}"#).unwrap();
    assert_eq!(policy.inactivity(), Duration::from_millis(25));
    assert_eq!(policy.resident_bytes().unwrap().get(), 4096);
    let without_resident = parse(r#"{"version":1,"inactivity_ms":50}"#).unwrap();
    let narrowed = policy.narrowed_by(without_resident);
    assert_eq!(narrowed.inactivity(), Duration::from_millis(25));
    assert_eq!(narrowed.resident_bytes(), policy.resident_bytes());
    let tighter_resident =
        cargo_util::ChildSupervision::new(Duration::from_millis(100), NonZeroU64::new(1024))
            .unwrap();
    assert_eq!(
        narrowed
            .narrowed_by(tighter_resident)
            .resident_bytes()
            .unwrap()
            .get(),
        1024
    );
}

#[test]
fn invalid_or_unbounded_policy_cannot_be_silently_ignored() {
    for input in [
        r#"{"version":2,"inactivity_ms":1}"#,
        r#"{"version":1,"inactivity_ms":0}"#,
        r#"{"version":1,"inactivity_ms":1,"resident_bytes":0}"#,
        r#"{"version":1,"inactivity_ms":1,"wall_ms":1}"#,
        r#"{"version":1,"inactivity_ms":1,"inactivity_ms":2}"#,
        r#"{"version":1,"inactivity_ms":18446744073709551616}"#,
    ] {
        assert!(parse(input).is_err(), "{input}");
    }
    assert!(parse(&" ".repeat(257)).is_err());
}
