use std::os::unix::process::ExitStatusExt;
use std::process::{ExitStatus, Output};

use super::CompletedProcess;

fn completed(stderr: &str) -> CompletedProcess {
    Output {
        status: ExitStatus::from_raw(0),
        stdout: Vec::new(),
        stderr: stderr.as_bytes().to_vec(),
    }
    .into()
}

#[test]
#[should_panic(expected = "needle was unexpectedly found in haystack")]
fn rejects_the_native_rustdoc_capitalized_ice_diagnostic() {
    completed("error: the compiler unexpectedly panicked. This is a bug\n").assert_not_ice();
}

#[test]
#[should_panic(expected = "needle was unexpectedly found in haystack")]
fn retains_the_lowercase_compiler_ice_rejection() {
    completed("error: the compiler unexpectedly panicked. this is a bug\n").assert_not_ice();
}

#[test]
fn ordinary_source_diagnostics_are_not_ice_reports() {
    completed("error[E0451]: field `private` of struct `Sealed` is private\n").assert_not_ice();
}
