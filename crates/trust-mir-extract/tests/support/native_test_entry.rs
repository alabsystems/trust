// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): the native entry of a trust-mir-extract
//! test binary. Its tests run the compiler in process, so its scheduler is
//! captured before libtest reads its arguments, opens a file or starts a
//! thread, and under `build-slot` protocol 1 the binary lends the compiler its
//! own execution (`capture_early_for_test_harness`). Shared by the library's
//! unit tests and each integration test.

extern crate rustc_data_structures;
extern crate test;

/// The generated test main constructs only static test references before
/// calling this.
pub(crate) fn main(tests: &[&test::TestDescAndFn]) {
    // SAFETY: first generated native-entry operation, before arbitrary callbacks.
    if let Err(error) =
        unsafe { rustc_data_structures::jobserver::capture_early_for_test_harness() }
    {
        eprintln!("trust-mir-extract test entry: inherited compiler scheduler refused: {error}");
        std::process::exit(75);
    }
    #[cfg(panic = "unwind")]
    let result = test::test_main_env_args(tests);
    #[cfg(not(panic = "unwind"))]
    let result = test::test_main_env_args_abort(tests);
    // Custom runners return unit; keep libtest's actual exit code.
    result.exit_process();
}
