//! A program runs under a sandbox that denies `process-info-setcontrol`.
//!
//! std's runtime init names the main thread before `main` (`pthread_setname_np`), and such a
//! sandbox refuses that call (-1, errno EPERM). A std built with debug assertions asserted the
//! call succeeded, so every program run there aborted before `main` with "fatal runtime error:
//! initialization or cleanup bug" (measured on macOS 27.0.1 with a toolchain whose std has
//! debug assertions on; `(deny process-info*)` refuses it too).

//@ only-apple
//@ ignore-cross-compile

use run_make_support::{bin_name, cmd, cwd, rustc};

fn main() {
    rustc().input("main.rs").run();
    for profile in [
        "(version 1)(allow default)(deny process-info-setcontrol)",
        "(version 1)(allow default)(deny process-info*)",
    ] {
        cmd("/usr/bin/sandbox-exec")
            .arg("-p")
            .arg(profile)
            .arg(cwd().join(bin_name("main")))
            .run()
            .assert_stdout_contains("started");
    }
}
