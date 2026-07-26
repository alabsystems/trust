use super::SessionFlipTelemetry;

#[test]
fn flip_telemetry_counts_paths_independently_and_saturates() {
    let mut telemetry = SessionFlipTelemetry::default();
    assert_eq!(telemetry.note_flipped(), 1);
    assert_eq!(telemetry.note_flipped(), 2);
    assert_eq!(telemetry.note_fallback(), 1);

    telemetry.flipped = usize::MAX;
    telemetry.fallbacks = usize::MAX;
    assert_eq!(telemetry.note_flipped(), usize::MAX);
    assert_eq!(telemetry.note_fallback(), usize::MAX);

    // A fresh state value is the model Session::with_trust_compiler_state constructs for
    // each compiler invocation; rustc_interface separately tests Session isolation itself.
    let fresh = SessionFlipTelemetry::default();
    assert_eq!(fresh.flipped, 0);
    assert_eq!(fresh.fallbacks, 0);
}
