//! Check that unstable name-resolution suggestions are omitted on stable.
//!
//! Regression test for <https://github.com/rust-lang/rust/issues/149402>.
//!
//@ only-nightly
//@ needs-target-std

use run_make_support::{diff, rustc, similar};

fn main() {
    let stable_like = rustc()
        .env("RUSTC_BOOTSTRAP", "-1")
        .edition("2024")
        .input("foo.rs")
        .run_fail()
        .stderr_utf8();

    assert!(!stable_like.contains("CoroutineState::Complete"));
    diff()
        .expected_file("stable.err")
        .actual_text("stable_like", &stable_like)
        // Trust: the `--explain` hint names the driver that was INVOKED
        // (`trustc` branded, `rustc` under `--trust-vanilla`), and one
        // snapshot is compared by both lanes. Fold it here so the snapshot
        // stays upstream-pristine.
        .normalize(r"trustc --explain", "rustc --explain")
        .run();

    let nightly = rustc().edition("2024").input("foo.rs").run_fail().stderr_utf8();

    assert!(nightly.contains("CoroutineState::Complete"));
    diff()
        .expected_file("nightly.err")
        .actual_text("nightly", &nightly)
        // Trust: the `--explain` hint names the driver that was INVOKED
        // (`trustc` branded, `rustc` under `--trust-vanilla`), and one
        // snapshot is compared by both lanes. Fold it here so the snapshot
        // stays upstream-pristine.
        .normalize(r"trustc --explain", "rustc --explain")
        .run();

    let stderr_diff =
        similar::TextDiff::from_lines(&stable_like, &nightly).unified_diff().to_string();
    diff().expected_file("output.diff").actual_text("diff", stderr_diff).run();
}
