//@ needs-target-std
//
// Rustc displays a compilation error when it finds a `mod` (module)
// statement referencing a file that does not exist. However, a bug from 2019
// caused invalid `mod` statements to silently insert empty inline modules
// instead of showing an error if the invalid `mod` statement had been passed
// through standard input. This test checks that this bug does not make a resurgence.
// See https://github.com/rust-lang/rust/issues/65601

// NOTE: This is not a UI test, because the bug which this test
// is checking for is specifically tied to passing
// `mod unknown;` through standard input.

use run_make_support::{diff, rustc};

fn main() {
    let out =
        rustc().edition("2015").crate_type("rlib").stdin_buf(b"mod unknown;").arg("-").run_fail();
    diff()
        .actual_text("actual-stdout", out.stdout_utf8())
        .expected_file("unknown-mod.stdout")
        .run();
    diff()
        .actual_text("actual-stderr", out.stderr_utf8())
        .expected_file("unknown-mod.stderr")
        .normalize(r#"\\"#, "/")
        // Trust: the `--explain` hint names the driver that was INVOKED
        // (`trustc` branded, `rustc` under `--trust-vanilla`), and one
        // snapshot is compared by both lanes. Fold it here so the snapshot
        // stays upstream-pristine.
        .normalize(r"trustc --explain", "rustc --explain")
        .run();
}
