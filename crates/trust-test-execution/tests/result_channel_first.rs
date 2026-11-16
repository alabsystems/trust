// The per-case result channel goes FIRST in a harness's arguments, so no test
// argument after it can swallow it (`trust_test_execution::results`).
//
// This test binary is its own tiny libtest harness: re-run with the fixture
// environment variable set, it has exactly two cases, one that fails and this
// driver, which then does nothing. With no name filter of its own, the
// harness's exit status is the whole suite's, which is what a swallowed
// channel used to turn green: `-- --` (or a trailing `--skip`) made
// `--logfile <file>` into name filters that matched nothing, so the harness
// ran 0 cases and exited 0.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(unix)]

use std::process::Command;

use trust_test_execution::results::{HarnessResultFiles, create_results_dir, is_logfile_arg};

/// Set only in a fixture run.
const FIXTURE_ENV: &str = "TRUST_TEST_EXECUTION_RESULT_CHANNEL_FIXTURE";

fn in_fixture() -> bool {
    std::env::var_os(FIXTURE_ENV).is_some()
}

/// The fixture's failing case; outside a fixture run it passes.
#[test]
fn fixture_case_fails() {
    assert!(!in_fixture(), "the fixture's failing case");
}

/// Run this binary as the fixture harness with exactly `argv`; its exit code
/// and the result file's contents, if it wrote one.
fn run(argv: &[String], logfile: &str) -> (Option<i32>, Option<String>) {
    let _ = std::fs::remove_file(logfile);
    let output = Command::new(std::env::current_exe().unwrap())
        .args(argv)
        .env(FIXTURE_ENV, "1")
        .output()
        .expect("run the fixture harness");
    (output.status.code(), std::fs::read_to_string(logfile).ok())
}

#[test]
fn no_test_argument_after_the_channel_turns_a_failing_suite_green() {
    if in_fixture() {
        return;
    }
    let root = tempfile_dir();
    let plan = root.join("prepared-tests.json");
    create_results_dir(&plan).unwrap();
    let files = HarnessResultFiles::for_harness(&plan, 0).unwrap();
    let failed_line = "failed fixture_case_fails\n";

    // Control: the fixture is sensitive to the order. With the channel LAST,
    // `--` swallows it and the failing suite exits 0, running nothing.
    let mut last = vec!["--".to_string()];
    last.extend(files.libtest_args());
    let (code, logfile) = run(&last, &files.logfile);
    assert_eq!(code, Some(0), "the defect this order had");
    assert_eq!(logfile, None, "and no result file");

    // Channel FIRST, as native Targo seals it: `--` only ends the options, so
    // every case runs, the failure is recorded and the harness exits 101.
    let (code, logfile) = run(&files.harness_args(&["--"]), &files.logfile);
    assert_eq!(code, Some(101));
    let logfile = logfile.expect("a result file");
    assert!(logfile.contains(failed_line), "{logfile:?}");
    assert!(logfile.contains("ok no_test_argument_after_the_channel"), "{logfile:?}");

    // A trailing value-taking option has nothing left to take: libtest's own
    // usage error, exit 101 with no result file (so never concluded).
    for option in ["--skip", "--color", "--test-threads"] {
        let (code, logfile) = run(&files.harness_args(&[option]), &files.logfile);
        assert_eq!(code, Some(101), "{option}");
        assert_eq!(logfile, None, "{option}");
    }
    // `--skip` naming the failing case is an ordinary filter, still honest.
    let (code, logfile) =
        run(&files.harness_args(&["--skip", "fixture_case_fails"]), &files.logfile);
    assert_eq!(code, Some(0));
    assert!(!logfile.unwrap().contains(failed_line));

    // A second channel never reaches a harness: native Targo refuses any
    // `--logfile` test argument (anywhere, `--` or not) before it seals the
    // plan, and the plan's validation refuses one (the crate's unit tests).
    // Had one got there after the first, libtest's own refusal is exit 101,
    // never a green, empty run.
    for second in [vec!["--logfile", "/elsewhere"], vec!["--logfile=/elsewhere"]] {
        assert!(second.iter().any(|arg| is_logfile_arg(arg)));
        let (code, logfile) = run(&files.harness_args(&second), &files.logfile);
        assert_eq!(code, Some(101), "{second:?}");
        assert_eq!(logfile, None, "{second:?}");
    }
    std::fs::remove_dir_all(&root).unwrap();
}

fn tempfile_dir() -> std::path::PathBuf {
    let root = std::env::temp_dir().join(format!(
        "trust-test-execution-channel-{}-{}",
        std::process::id(),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
    ));
    std::fs::create_dir_all(&root).unwrap();
    root
}
