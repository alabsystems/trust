//! VCGEN-TEST-BACKSTOP-1: the test router's backstop may be raised by
//! `TRUST_TEST_SOLVER_BACKSTOP_MS`, never lowered, and a malformed override is an
//! error rather than the default. Pinned on the pure parser so no test mutates the
//! process environment the solver tests read.

use crate::test_router::{TEST_BACKSTOP_MAX_MS, TEST_BACKSTOP_MS, test_backstop_ms_from};

#[test]
fn unset_or_blank_override_is_the_default() {
    assert_eq!(test_backstop_ms_from(None), TEST_BACKSTOP_MS);
    assert_eq!(test_backstop_ms_from(Some("")), TEST_BACKSTOP_MS);
    assert_eq!(test_backstop_ms_from(Some("  ")), TEST_BACKSTOP_MS);
}

#[test]
fn an_override_never_lowers_the_backstop() {
    for low in ["0", "1", "5000", "30000", "599999"] {
        assert_eq!(test_backstop_ms_from(Some(low)), TEST_BACKSTOP_MS, "{low}");
    }
}

#[test]
fn an_override_raises_the_backstop_up_to_the_ceiling() {
    assert_eq!(test_backstop_ms_from(Some("600000")), TEST_BACKSTOP_MS);
    assert_eq!(test_backstop_ms_from(Some(" 1800000 ")), 1_800_000);
    assert_eq!(test_backstop_ms_from(Some("86400000")), TEST_BACKSTOP_MAX_MS);
    // A deadline `Instant` cannot represent reads as already passed, so the
    // ceiling keeps a huge override from ending every solve at once.
    assert_eq!(test_backstop_ms_from(Some("18446744073709551615")), TEST_BACKSTOP_MAX_MS);
}

#[test]
#[should_panic(expected = "must be a whole number of milliseconds")]
fn a_malformed_override_is_an_error_not_the_default() {
    test_backstop_ms_from(Some("10m"));
}
