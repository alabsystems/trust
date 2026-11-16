//! Actual-source native controls and actual front-end MIR through vcgen/AY/Clean.
//! A certified row certifies its formula, not the source-to-formula translation.
use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "fixtures/str-bytes-count/count_bytes.rs"]
mod source;
#[path = "support/test_router.rs"]
mod test_router;

fn overflow_rows(name: &str) -> Vec<(VerificationResult, bool)> {
    let path = format!("{}/tests/fixtures/str-bytes-count/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let f: VerifiableFunction =
        serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&f);
            let router = test_router::deterministic_test_router();
            vcs.into_iter()
                .filter(|vc| matches!(&vc.kind, VcKind::ArithmeticOverflow { .. }))
                .map(|vc| {
                    let result = router.verify_all(std::slice::from_ref(&vc)).remove(0).1;
                    let certified = trust_certify::certify_vc(&vc).is_some();
                    (result, certified)
                })
                .collect()
        })
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn the_real_byte_count_addition_has_a_certified_overflow_row() {
    let rows = overflow_rows("bytes_count");
    assert!(!rows.is_empty(), "positive control must retain an overflow obligation");
    assert!(
        rows.iter()
            .all(|(r, certified)| matches!(r, VerificationResult::Proved { .. }) && *certified),
        "{rows:?}"
    );
}

#[test]
fn real_invalid_sources_keep_their_overflow_refusal() {
    for name in [
        "bytes_count_underflow",
        "split_count_not_bounded_by_bytes",
        "reassigned_root",
        "custom_count_must_overflow",
    ] {
        let rows = overflow_rows(name);
        assert!(!rows.is_empty(), "{name} must retain an overflow obligation");
        assert!(
            rows.iter().any(|(r, _)| !matches!(r, VerificationResult::Proved { .. })),
            "{name}: {rows:?}"
        );
    }
}

#[test]
fn the_same_sources_execute_the_valid_and_invalid_paths() {
    assert_eq!(source::bytes_count(""), 1);
    assert_eq!(source::bytes_count("é\n猫\n"), 3);
    assert!(std::panic::catch_unwind(|| source::bytes_count_underflow("")).is_err());
    assert!(std::panic::catch_unwind(|| source::split_count_not_bounded_by_bytes("")).is_err());
    assert!(std::panic::catch_unwind(|| source::reassigned_root("long", "")).is_err());
    assert!(std::panic::catch_unwind(source::custom_count_must_overflow).is_err());
}
