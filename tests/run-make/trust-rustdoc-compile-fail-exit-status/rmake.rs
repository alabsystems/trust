//! Trust: compile_fail requires an ordinary source rejection, not any failed
//! compiler process. In particular native custody exit 75 must fail the test.

//@ needs-target-std

use run_make_support::{bare_rustc, path, rustdoc};

fn main() {
    let builder = path("status-builder");
    // The controlled exit fixture carries no compiler or proof authority.
    bare_rustc().input("builder.rs").arg("-Ztrust-verify=off").output(&builder).run();
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        let signal = run_make_support::cmd(&builder)
            .env("TEST_BUILDER_EXIT", "signal")
            .stdin_buf(b"protocol source")
            .run_fail();
        assert_eq!(signal.status().signal(), Some(15));
    }
    for mode in ["0", "1", "75", "panic"].iter().copied().chain(cfg!(unix).then_some("signal")) {
        let mut command = rustdoc();
        command
            .input("doc.rs")
            .arg("--test")
            .arg("-Zunstable-options")
            .arg("--test-builder")
            .arg(&builder)
            .env("TEST_BUILDER_EXIT", mode);
        if mode == "1" {
            command.run().assert_stdout_contains("1 passed; 0 failed");
        } else {
            let output = command.run_fail();
            output.assert_stdout_contains("0 passed; 1 failed");
            output.assert_not_ice();
        }
    }
}
