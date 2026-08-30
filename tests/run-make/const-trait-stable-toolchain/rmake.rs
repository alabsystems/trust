//@ needs-target-std
//
// Test output of const super trait errors in both stable and nightly.
// We don't want to provide suggestions on stable that only make sense in nightly.

use run_make_support::{diff, rustc};

fn main() {
    let out = rustc()
        .input("const-super-trait.rs")
        .env("RUSTC_BOOTSTRAP", "-1")
        .cfg("feature_enabled")
        .run_fail()
        .assert_stderr_not_contains("as `const` to allow it to have `const` implementations")
        .stderr_utf8();
    diff()
        .expected_file("const-super-trait-stable-enabled.stderr")
        // Trust: the `--explain` hint names the driver that was INVOKED
        // (`trustc` branded, `rustc` under `--trust-vanilla`), and one
        // snapshot is compared by both lanes. Fold it so the snapshot
        // stays upstream-pristine.
        .normalize(r"trustc --explain", "rustc --explain")
        .normalize(
            "may not be used on the .* release channel",
            "may not be used on the NIGHTLY release channel",
        )
        .actual_text("(rustc)", &out)
        .run();
    let out = rustc()
        .input("const-super-trait.rs")
        .cfg("feature_enabled")
        .ui_testing()
        .run_fail()
        .assert_stderr_not_contains("enable `#![feature(const_trait_impl)]` in your crate and mark")
        .assert_stderr_contains("as `const` to allow it to have `const` implementations")
        .stderr_utf8();
    diff()
        .expected_file("const-super-trait-nightly-enabled.stderr")
        // Trust: the `--explain` hint names the driver that was INVOKED
        // (`trustc` branded, `rustc` under `--trust-vanilla`), and one
        // snapshot is compared by both lanes. Fold it so the snapshot
        // stays upstream-pristine.
        .normalize(r"trustc --explain", "rustc --explain")
        .actual_text("(rustc)", &out)
        .run();
    let out = rustc()
        .input("const-super-trait.rs")
        .env("RUSTC_BOOTSTRAP", "-1")
        .run_fail()
        .assert_stderr_not_contains("enable `#![feature(const_trait_impl)]` in your crate and mark")
        .assert_stderr_not_contains("as `const` to allow it to have `const` implementations")
        .stderr_utf8();
    diff()
        .expected_file("const-super-trait-stable-disabled.stderr")
        // Trust: the `--explain` hint names the driver that was INVOKED
        // (`trustc` branded, `rustc` under `--trust-vanilla`), and one
        // snapshot is compared by both lanes. Fold it so the snapshot
        // stays upstream-pristine.
        .normalize(r"trustc --explain", "rustc --explain")
        .actual_text("(rustc)", &out)
        .run();
    let out = rustc()
        .input("const-super-trait.rs")
        .ui_testing()
        .run_fail()
        .assert_stderr_contains("enable `#![feature(const_trait_impl)]` in your crate and mark")
        .stderr_utf8();
    diff()
        .expected_file("const-super-trait-nightly-disabled.stderr")
        // Trust: the `--explain` hint names the driver that was INVOKED
        // (`trustc` branded, `rustc` under `--trust-vanilla`), and one
        // snapshot is compared by both lanes. Fold it so the snapshot
        // stays upstream-pristine.
        .normalize(r"trustc --explain", "rustc --explain")
        .actual_text("(rustc)", &out)
        .run();
}
