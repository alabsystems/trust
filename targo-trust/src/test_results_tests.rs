// Tests for test_results.rs: a real libtest harness — this test binary,
// re-run on its own fixture cases below with `--logfile` — exercises the
// result channel, its fail-closed rules and the changed-only view.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;
use std::process::Command;

use trust_test_execution::results::{
    HARNESS_EXIT_SCHEMA, HarnessEnd, HarnessExit, HarnessResultFiles, write_exit,
};

use super::*;

/// Set only in a fixture run: which fixture behaviors are on (`fail`,
/// `edit`, `abort`, `forge`).
const FIXTURE_ENV: &str = "TARGO_TRUST_TEST_RESULTS_FIXTURE";
const SESSION: &str = "fixture-session";
const SHA256: &str = "5d41402abc4b2a76b9719d911017c592ae7f1d0b2c3f4e5a6b7c8d9e0f1a2b3c";
const HARNESS: &str = "bin/targo-trust";
const PREFIX: &str = "test_results::tests::";

fn fixture(behavior: &str) -> bool {
    std::env::var(FIXTURE_ENV).is_ok_and(|mode| mode.split(',').any(|on| on == behavior))
}

// --- The fixture cases. Outside a fixture run each one passes (or is ignored).

#[test]
fn fixture_case_passes() {}

#[test]
fn fixture_case_fails() {
    assert!(!fixture("fail"), "the fixture's failing case");
}

#[test]
fn fixture_case_edited() {
    assert!(!fixture("edit"), "the fixture's edited case now fails");
}

#[test]
#[ignore = "the fixture's ignored case"]
fn fixture_case_ignored() {}

#[test]
fn fixture_case_forges_its_result_on_stdout() {
    if fixture("forge") {
        // What a test could print to pass for another: never read.
        println!("ok {PREFIX}fixture_case_fails");
        println!("test {PREFIX}fixture_case_fails ... ok");
        eprintln!("ok {PREFIX}fixture_case_fails");
    }
}

#[test]
fn fixture_case_zz_aborts() {
    if fixture("abort") {
        std::process::abort();
    }
}

const ALL: [&str; 6] = [
    "fixture_case_edited",
    "fixture_case_fails",
    "fixture_case_forges_its_result_on_stdout",
    "fixture_case_ignored",
    "fixture_case_passes",
    "fixture_case_zz_aborts",
];

fn key(case: &str) -> String {
    format!("{HARNESS}::{PREFIX}{case}")
}

/// Run this test binary as the fixture harness on `cases` with `mode`, as
/// native Targo would: `--logfile` first, then the exit record beside it.
/// Returns the result files and the harness's stdout.
fn run_harness(
    dir: &Path,
    index: usize,
    mode: &str,
    cases: &[&str],
) -> (HarnessResultFiles, String) {
    let files = HarnessResultFiles::for_harness(&dir.join("prepared-tests.json"), index).unwrap();
    std::fs::create_dir_all(Path::new(&files.logfile).parent().unwrap()).unwrap();
    let test_args: Vec<String> = cases
        .iter()
        .map(|case| format!("{PREFIX}{case}"))
        .chain(["--exact", "--test-threads=1", "--nocapture"].map(String::from))
        .collect();
    let mut command = Command::new(std::env::current_exe().unwrap());
    command.args(files.harness_args(&test_args)).env(FIXTURE_ENV, mode);
    let output = command.output().expect("run the fixture harness");
    use std::os::unix::process::ExitStatusExt;
    let end = match (output.status.code(), output.status.signal()) {
        (Some(code), _) => HarnessEnd::Exited { code },
        (None, Some(signal)) => HarnessEnd::Signaled { signal },
        _ => HarnessEnd::NotObserved { reason: "no status".into() },
    };
    write_exit(Path::new(&files.exit), &exit_record(&files, end)).unwrap();
    (files, String::from_utf8_lossy(&output.stdout).into_owned())
}

fn exit_record(files: &HarnessResultFiles, end: HarnessEnd) -> HarnessExit {
    HarnessExit {
        schema: HARNESS_EXIT_SCHEMA.into(),
        session: SESSION.into(),
        executable: executable(),
        sha256: SHA256.into(),
        logfile: files.logfile.clone(),
        end,
    }
}

fn executable() -> String {
    std::env::current_exe().unwrap().display().to_string()
}

fn identity(executable: &str) -> HarnessIdentity<'_> {
    HarnessIdentity { session: SESSION, executable, sha256: SHA256 }
}

fn rows_of(files: &HarnessResultFiles) -> PackageTests {
    let executable = executable();
    harness_rows(HARNESS, &observe(files, identity(&executable)))
}

fn outcomes(tests: &PackageTests) -> Vec<(String, CaseOutcome)> {
    tests.cases.iter().map(|case| (case.key.clone(), case.outcome)).collect()
}

#[test]
fn a_harness_that_ran_to_its_end_reports_each_case_as_its_harness_did() {
    let dir = tempfile::tempdir().unwrap();
    let cases = [
        "fixture_case_fails",
        "fixture_case_forges_its_result_on_stdout",
        "fixture_case_ignored",
        "fixture_case_passes",
    ];
    let (files, stdout) = run_harness(dir.path(), 0, "fail,forge", &cases);
    // The forged lines reached the output stream, and changed nothing.
    assert!(stdout.contains(&format!("ok {PREFIX}fixture_case_fails\n")), "{stdout}");
    let tests = rows_of(&files);
    assert_eq!(
        tests.harnesses,
        vec![TestHarnessRecord { key: HARNESS.into(), concluded: true, reason: None }]
    );
    assert_eq!(
        outcomes(&tests),
        vec![
            (key("fixture_case_fails"), CaseOutcome::Failed),
            (key("fixture_case_forges_its_result_on_stdout"), CaseOutcome::Passed),
            (key("fixture_case_ignored"), CaseOutcome::Ignored),
            (key("fixture_case_passes"), CaseOutcome::Passed),
        ]
    );
}

#[test]
fn a_harness_ended_by_a_signal_concludes_nothing_and_keeps_its_failures() {
    let dir = tempfile::tempdir().unwrap();
    let cases = ["fixture_case_fails", "fixture_case_passes", "fixture_case_zz_aborts"];
    let (files, _) = run_harness(dir.path(), 0, "fail,abort", &cases);
    let tests = rows_of(&files);
    assert_eq!(
        tests.harnesses,
        vec![TestHarnessRecord {
            key: HARNESS.into(),
            concluded: false,
            reason: Some(format!("ended by signal {}", libc::SIGABRT)),
        }]
    );
    // The abort's own case has no line; the pass before it is not a pass.
    assert_eq!(
        outcomes(&tests),
        vec![
            (key("fixture_case_fails"), CaseOutcome::Failed),
            (key("fixture_case_passes"), CaseOutcome::NotConcluded),
        ]
    );
}

#[test]
fn a_missing_truncated_or_disagreeing_result_file_is_never_a_pass() {
    let dir = tempfile::tempdir().unwrap();
    let (files, _) = run_harness(dir.path(), 0, "", &["fixture_case_passes"]);
    let complete = std::fs::read(&files.logfile).unwrap();
    assert_eq!(complete, format!("ok {PREFIX}fixture_case_passes\n").into_bytes());
    assert!(rows_of(&files).harnesses[0].concluded);
    let executable = executable();
    let observed = |end: HarnessEnd, file: Result<Vec<u8>, String>| {
        harness_rows(HARNESS, &HarnessObservation { end: Ok(end), result_file: file })
    };
    let refused = |tests: PackageTests, why: &str| {
        let harness = &tests.harnesses[0];
        assert!(!harness.concluded, "{why}");
        assert!(harness.reason.as_deref().unwrap().contains(why), "{harness:?}");
        assert!(
            tests.cases.iter().all(|case| case.outcome != CaseOutcome::Passed),
            "{why}: {tests:?}"
        );
    };
    // Truncated: the last line is unfinished.
    refused(
        observed(HarnessEnd::Exited { code: 0 }, Ok(complete[..complete.len() - 1].to_vec())),
        "truncated",
    );
    // A result file reporting a failure under status 0, and status 101 with none.
    refused(
        observed(HarnessEnd::Exited { code: 0 }, Ok(b"failed x\n".to_vec())),
        "reports a failed case",
    );
    refused(observed(HarnessEnd::Exited { code: 101 }, Ok(complete.clone())), "no failed case");
    refused(observed(HarnessEnd::Exited { code: 3 }, Ok(complete.clone())), "status 3");
    refused(observed(HarnessEnd::Exited { code: 0 }, Ok(b"ok a\nok a\n".to_vec())), "twice");
    refused(
        observed(HarnessEnd::Exited { code: 0 }, Ok(b"running 1 test\n".to_vec())),
        "not a libtest",
    );
    refused(observed(HarnessEnd::Exited { code: 0 }, Ok(vec![0xff, b'\n'])), "UTF-8");
    refused(
        observed(HarnessEnd::NotObserved { reason: "cancelled".into() }, Ok(complete.clone())),
        "cancelled",
    );
    // An exit record of another harness, then none at all.
    let other = dir.path().join("other.exit");
    let mut record = exit_record(&files, HarnessEnd::Exited { code: 0 });
    record.executable = "/elsewhere".into();
    write_exit(&other, &record).unwrap();
    let foreign = HarnessResultFiles { exit: other.display().to_string(), ..files.clone() };
    refused(harness_rows(HARNESS, &observe(&foreign, identity(&executable))), "another harness");
    std::fs::remove_file(&files.exit).unwrap();
    refused(rows_of(&files), "no exit record");
    // A missing result file, with a good exit record.
    write_exit(Path::new(&files.exit), &exit_record(&files, HarnessEnd::Exited { code: 0 }))
        .unwrap();
    std::fs::remove_file(&files.logfile).unwrap();
    refused(rows_of(&files), "no readable result file");
    assert!(rows_of(&files).cases.is_empty());
}

#[test]
fn a_case_reported_twice_is_failed_when_any_of_its_lines_is() {
    // A test can write a forged `ok <its own name>` line through libtest's
    // file descriptor before libtest writes its real `failed` line: the
    // repetition leaves the harness not concluded, and the failure stays.
    for code in [0, LIBTEST_FAILED_STATUS] {
        for file in [&b"ok a\nfailed a\nok b\n"[..], &b"failed a\nok a\nok b\n"[..]] {
            let tests = harness_rows(
                HARNESS,
                &HarnessObservation {
                    end: Ok(HarnessEnd::Exited { code }),
                    result_file: Ok(file.to_vec()),
                },
            );
            let harness = &tests.harnesses[0];
            assert!(!harness.concluded, "{code}: {harness:?}");
            assert!(harness.reason.as_deref().unwrap().contains("`a` twice"), "{harness:?}");
            assert_eq!(
                outcomes(&tests),
                vec![
                    (format!("{HARNESS}::a"), CaseOutcome::Failed),
                    (format!("{HARNESS}::b"), CaseOutcome::NotConcluded),
                ],
                "status {code}, file {:?}",
                String::from_utf8_lossy(file)
            );
        }
    }
}

#[test]
fn a_failure_after_a_line_that_is_not_a_result_line_stays_failed() {
    let rows = |code: i32, file: &[u8]| {
        harness_rows(
            HARNESS,
            &HarnessObservation {
                end: Ok(HarnessEnd::Exited { code }),
                result_file: Ok(file.to_vec()),
            },
        )
    };
    // Libtest's own timed failure (`--ensure-time`) is a result line.
    let timed =
        rows(LIBTEST_FAILED_STATUS, b"ok a\nfailed (time limit exceeded) b <1.000s>\nfailed c\n");
    assert!(timed.harnesses[0].concluded, "{timed:?}");
    assert_eq!(
        outcomes(&timed),
        vec![
            (format!("{HARNESS}::a"), CaseOutcome::Passed),
            (format!("{HARNESS}::b"), CaseOutcome::Failed),
            (format!("{HARNESS}::c"), CaseOutcome::Failed),
        ]
    );
    assert_eq!(
        outcomes(&rows(LIBTEST_FAILED_STATUS, b"failed (time limit exceeded) b\n")),
        vec![(format!("{HARNESS}::b"), CaseOutcome::Failed)]
    );
    // A line that is not a result line leaves the harness not concluded, and
    // every failure the file reports after it keeps its row; nothing passes.
    for code in [0, LIBTEST_FAILED_STATUS] {
        let tests = rows(
            code,
            b"ok a\nfailed b\nnot a result line\nok d\nfailed x y e\nignored f\nfailed: m\n  \
              more g\n",
        );
        let harness = &tests.harnesses[0];
        assert!(!harness.concluded, "{code}: {harness:?}");
        assert!(
            harness
                .reason
                .as_deref()
                .unwrap()
                .contains("result line 3 is not a libtest result line"),
            "{harness:?}"
        );
        assert_eq!(
            outcomes(&tests),
            vec![
                (format!("{HARNESS}::a"), CaseOutcome::NotConcluded),
                (format!("{HARNESS}::b"), CaseOutcome::Failed),
                (format!("{HARNESS}::d"), CaseOutcome::NotConcluded),
                (format!("{HARNESS}::e"), CaseOutcome::Failed),
                (format!("{HARNESS}::f"), CaseOutcome::NotConcluded),
                (format!("{HARNESS}::g"), CaseOutcome::Failed),
            ],
            "status {code}"
        );
    }
    // A record that names no case is a problem, and reading goes on.
    let nameless = rows(LIBTEST_FAILED_STATUS, b"ok \nfailed c\n");
    assert!(!nameless.harnesses[0].concluded, "{nameless:?}");
    assert_eq!(outcomes(&nameless), vec![(format!("{HARNESS}::c"), CaseOutcome::Failed)]);
}

#[test]
fn libtest_result_lines_with_messages_and_times_parse_to_their_names() {
    let parsed = parse_result_file(
        b"ok a::b\nignored: slow on CI c::d\nfailed: panic did not contain expected string\n      \
          panic message: \"x y\"\n expected substring: \"z\" e::f\nok g <0.003s>\nfailed h\n",
    );
    assert_eq!(parsed.problem, None);
    let names: Vec<(Reported, &str)> =
        parsed.cases.iter().map(|(word, name)| (*word, name.as_str())).collect();
    assert_eq!(
        names,
        [
            (Reported::Ok, "a::b"),
            (Reported::Ignored, "c::d"),
            (Reported::Failed, "e::f"),
            (Reported::Ok, "g"),
            (Reported::Failed, "h"),
        ]
    );
    assert!(parse_result_file(b"ok a b\n").problem.is_some(), "a plain line names one case");
    assert!(parse_result_file(b"").problem.is_none() && parse_result_file(b"").cases.is_empty());
}

#[test]
fn a_harness_with_no_result_channel_or_never_started_is_not_concluded() {
    let harnesses = [AuthorizedHarness {
        package: "fixture".into(),
        key: HARNESS.into(),
        executable: "/target/debug/deps/fixture-0".into(),
    }];
    let not_run =
        collect(&harnesses, Execution::NotRun("the frontend proof gate did not pass".into()));
    assert_eq!(
        not_run["fixture"].harnesses[0].reason.as_deref(),
        Some("not run: the frontend proof gate did not pass")
    );
    let plan = trust_test_execution::PreparedTests {
        schema: trust_test_execution::PLAN_SCHEMA.into(),
        session: SESSION.into(),
        host_os: std::env::consts::OS.into(),
        host_arch: std::env::consts::ARCH.into(),
        target_directory: "/target".into(),
        no_fail_fast: false,
        tests: vec![trust_test_execution::PreparedTest {
            target: "fixture".into(),
            executable: "/target/debug/deps/fixture-0".into(),
            sha256: SHA256.into(),
            size: 1,
            cwd: "/".into(),
            args: Vec::new(),
            env: Default::default(),
            results: None,
        }],
    };
    let old = collect(&harnesses, Execution::Ran { session: SESSION, plan: &plan });
    let harness = &old["fixture"].harnesses[0];
    assert!(!harness.concluded);
    assert!(harness.reason.as_deref().unwrap().contains("records no per-case results"));
    assert!(old["fixture"].cases.is_empty());
}

// --- The changed-only view, end to end over real harness runs.

fn record_bytes(arguments: &[String], tests: &PackageTests) -> String {
    let header = crate::obligations::RecordHeader {
        package: "fixture",
        lane: "strict",
        policy: "strict",
        selection: "default",
        targo_trust_commit: "c",
        profile: "p",
        outcome: "measured",
        vector: "v",
        coverage_complete: true,
        concluded: true,
        degraded_anchors: 0,
    };
    crate::obligations::render_package_ndjson_with_tests(
        &header,
        &[],
        Some((arguments, tests)),
        &crate::obligations::PackageRecords::new(),
    )
}

/// One `targo trust test` of the fixture as `mode`, through the record and the
/// caller's snapshots: the view's lines.
fn delta_run(target: &Path, runs: &Path, run: usize, mode: &str) -> Vec<String> {
    let (files, _) = run_harness(&runs.join(run.to_string()), 0, mode, &ALL);
    let tests = rows_of(&files);
    let bytes = record_bytes(&[], &tests);
    let parsed = crate::obligations::parse_package_ndjson(&bytes).expect("the record reads back");
    assert_eq!(parsed.tests, Some(Vec::new()));
    assert_eq!(parsed.test_cases, tests.cases);
    crate::agent_delta::publish_shown(
        target,
        &[("fixture".to_string(), bytes)],
        &crate::agent_delta::DeltaRequest::default(),
        Some("agent"),
        false,
    )
    .lines()
}

fn summary(lines: &[String]) -> &str {
    lines.last().expect("a summary line")
}

#[test]
fn a_test_run_prints_only_the_cases_that_changed_and_one_line_when_nothing_did() {
    let target = tempfile::tempdir().unwrap();
    let runs = tempfile::tempdir().unwrap();
    let truth = "(reported by each test binary's own harness)";

    // First run: no base; nothing failed, so the summary alone.
    let first = delta_run(target.path(), runs.path(), 0, "forge");
    assert_eq!(first.len(), 1, "{first:#?}");
    assert!(
        summary(&first).starts_with(&format!(
            "fixture  0 obligation(s); 6 test case(s): 5 passed, 0 failed, 1 ignored, 0 not \
             concluded {truth}  (now "
        )),
        "{first:#?}"
    );

    // A rerun with nothing changed: one line.
    let again = delta_run(target.path(), runs.path(), 1, "forge");
    assert_eq!(again.len(), 1, "{again:#?}");
    assert!(summary(&again).contains("; 0 of 6 test case(s) changed: 5 passed"), "{again:#?}");

    // Editing one test makes it fail: only its row.
    let edited = delta_run(target.path(), runs.path(), 2, "forge,edit");
    assert_eq!(
        edited[..edited.len() - 1],
        [format!(
            "NEW FAILED  [TEST failed]  {}  test  failed (was passed)  reported by its harness  -",
            key("fixture_case_edited")
        )],
        "{edited:#?}"
    );
    assert!(summary(&edited).contains("; 1 of 6 test case(s) changed: 4 passed, 1 failed"));

    // A failing case prints on every run, as a failing obligation does.
    let still = delta_run(target.path(), runs.path(), 3, "forge,edit");
    assert_eq!(
        still[..still.len() - 1],
        [format!(
            "STILL       [TEST failed]  {}  test  failed  reported by its harness  -",
            key("fixture_case_edited")
        )],
        "{still:#?}"
    );
    assert!(summary(&still).contains("; 0 of 6 test case(s) changed"));

    // Fixed: the row says so once, then nothing.
    let fixed = delta_run(target.path(), runs.path(), 4, "forge");
    assert_eq!(
        fixed[..fixed.len() - 1],
        [format!(
            "CHANGED     [TEST passed]  {}  test  passed (was failed)  reported by its harness  -",
            key("fixture_case_edited")
        )],
        "{fixed:#?}"
    );
    assert_eq!(delta_run(target.path(), runs.path(), 5, "forge").len(), 1);

    // A crash: the harness row, and no case is a pass any more.
    let crashed = delta_run(target.path(), runs.path(), 6, "forge,abort");
    assert!(
        crashed.contains(&format!(
            "CHANGED     [TEST HARNESS not concluded]  {HARNESS}  harness  not concluded: ended \
             by signal {} (was concluded)  reported by its harness  -",
            libc::SIGABRT
        )),
        "{crashed:#?}"
    );
    assert!(crashed.iter().all(|line| !line.contains("[TEST passed]")), "{crashed:#?}");
    assert!(
        crashed.contains(&format!(
            "CHANGED     [TEST not concluded]  {}  test  not concluded (was passed)  reported by \
             its harness  -",
            key("fixture_case_passes")
        )),
        "{crashed:#?}"
    );
    assert!(summary(&crashed).contains("1 harness(es) not concluded"), "{crashed:#?}");
    // Still crashing: every row that is not a pass prints again.
    let again = delta_run(target.path(), runs.path(), 7, "forge,abort");
    assert!(again.len() > 1);
    assert!(again[..again.len() - 1].iter().all(|line| line.starts_with("STILL")), "{again:#?}");

    // No proof word, ever.
    for line in first.iter().chain(&edited).chain(&still).chain(&fixed).chain(&crashed) {
        for word in ["PROVED", "proved", "proof", "verified", "certified", "Certified"] {
            assert!(!line.contains(word), "`{word}` in {line}");
        }
    }
}

#[test]
fn a_test_run_is_never_compared_with_a_check() {
    let target = tempfile::tempdir().unwrap();
    let runs = tempfile::tempdir().unwrap();
    let check = crate::obligations::render_package_ndjson(
        &crate::obligations::RecordHeader {
            package: "fixture",
            lane: "strict",
            policy: "strict",
            selection: "default",
            targo_trust_commit: "c",
            profile: "p",
            outcome: "measured",
            vector: "v",
            coverage_complete: true,
            concluded: true,
            degraded_anchors: 0,
        },
        &crate::obligations::PackageRecords::new(),
    );
    let request = crate::agent_delta::DeltaRequest::default();
    let view = crate::agent_delta::publish_shown(
        target.path(),
        &[("fixture".to_string(), check)],
        &request,
        Some("agent"),
        false,
    );
    let token = view.packages[0].now.clone().unwrap();
    // The test run after a check has no base: the caller's pointer is the
    // check's, under another measurement.
    let test = delta_run(target.path(), runs.path(), 0, "");
    assert!(summary(&test).contains("; 6 test case(s):"), "{test:#?}");
    // `--since` naming the check's snapshot is refused for a test run.
    let (files, _) = run_harness(&runs.path().join("since"), 0, "", &ALL);
    let since = crate::agent_delta::publish_shown(
        target.path(),
        &[("fixture".to_string(), record_bytes(&[], &rows_of(&files)))],
        &crate::agent_delta::DeltaRequest { since: Some(token.clone()), all_rows: false },
        Some("agent"),
        false,
    )
    .lines();
    assert!(
        since.iter().any(|line| line
            == &format!(
                "note: snapshot {token} is a check run's and this is a test run's; no base"
            )),
        "{since:#?}"
    );
}

#[test]
fn a_test_run_given_other_arguments_is_never_the_base() {
    let target = tempfile::tempdir().unwrap();
    let runs = tempfile::tempdir().unwrap();
    // The whole fixture, twice: the second run has the first as its base.
    delta_run(target.path(), runs.path(), 0, "");
    let whole = delta_run(target.path(), runs.path(), 1, "");
    assert!(summary(&whole).contains("; 0 of 6 test case(s) changed"), "{whole:#?}");
    let token = crate::agent_delta::publish_shown(
        target.path(),
        &[(
            "fixture".to_string(),
            record_bytes(&[], &rows_of(&run_harness(&runs.path().join("2"), 0, "", &ALL).0)),
        )],
        &crate::agent_delta::DeltaRequest::default(),
        Some("other"),
        false,
    )
    .packages[0]
        .now
        .clone()
        .unwrap();
    // A filtered run names other cases: compared with the whole run, every
    // case it did not run would vanish. Its pointer is its own, so it has no
    // base, and `--since` naming the whole run's snapshot says why.
    let (files, _) = run_harness(&runs.path().join("3"), 0, "", &["fixture_case_passes"]);
    let filtered = ["--exact".to_string(), "fixture_case_passes".to_string()];
    let publish = |request: &crate::agent_delta::DeltaRequest| {
        crate::agent_delta::publish_shown(
            target.path(),
            &[("fixture".to_string(), record_bytes(&filtered, &rows_of(&files)))],
            request,
            Some("agent"),
            false,
        )
        .lines()
    };
    let first = publish(&crate::agent_delta::DeltaRequest::default());
    assert_eq!(first.len(), 1, "{first:#?}");
    assert!(summary(&first).contains("; 1 test case(s): 1 passed"), "{first:#?}");
    assert!(first.iter().all(|line| !line.starts_with("VANISHED")), "{first:#?}");
    let since =
        publish(&crate::agent_delta::DeltaRequest { since: Some(token.clone()), all_rows: false });
    assert!(
        since.iter().any(|line| line
            == &format!(
                "note: snapshot {token}'s test harnesses were given `` and this run's \
                 `--exact fixture_case_passes`; no base"
            )),
        "{since:#?}"
    );
}

#[test]
fn a_harness_row_that_changed_is_never_counted_as_a_changed_case() {
    let target = tempfile::tempdir().unwrap();
    let truth = "(reported by each test binary's own harness)";
    let publish = |end: HarnessEnd, file: &[u8]| {
        let tests = harness_rows(
            HARNESS,
            &HarnessObservation { end: Ok(end), result_file: Ok(file.to_vec()) },
        );
        let view = crate::agent_delta::publish_shown(
            target.path(),
            &[("fixture".to_string(), record_bytes(&[], &tests))],
            &crate::agent_delta::DeltaRequest::default(),
            Some("agent"),
            false,
        );
        let now = view.packages[0].now.clone().unwrap();
        (view.lines(), now)
    };
    // A harness with no case lines concluded, then killed: only its row
    // changed, so no test case changed.
    let (_, base) = publish(HarnessEnd::Exited { code: 0 }, b"");
    let (killed, now) = publish(HarnessEnd::Signaled { signal: 9 }, b"");
    assert_eq!(
        killed,
        [
            format!(
                "CHANGED     [TEST HARNESS not concluded]  {HARNESS}  harness  not concluded: \
                 ended by signal 9 (was concluded)  reported by its harness  -"
            ),
            format!(
                "fixture  0 of 0 changed since {base}; 0 of 0 test case(s) changed: 0 passed, 0 \
                 failed, 0 ignored, 0 not concluded, 1 harness(es) not concluded {truth}  (now \
                 {now})"
            ),
        ]
    );
    // A harness that ends otherwise, its one failed case unchanged: the
    // harness row is CHANGED and the case STILL, and no test case changed.
    let (_, base) = publish(HarnessEnd::Signaled { signal: 6 }, b"failed a\n");
    let (other_end, now) = publish(HarnessEnd::Signaled { signal: 9 }, b"failed a\n");
    assert_eq!(
        other_end,
        [
            format!(
                "CHANGED     [TEST HARNESS not concluded]  {HARNESS}  harness  not concluded: \
                 ended by signal 9 (was not concluded: ended by signal 6)  reported by its \
                 harness  -"
            ),
            format!(
                "STILL       [TEST failed]  {HARNESS}::a  test  failed  reported by its harness  -"
            ),
            format!(
                "fixture  0 of 0 changed since {base}; 0 of 1 test case(s) changed: 0 passed, 1 \
                 failed, 0 ignored, 0 not concluded, 1 harness(es) not concluded {truth}  (now \
                 {now})"
            ),
        ]
    );
}

#[test]
fn a_base_failure_missing_from_a_harness_that_did_not_conclude_still_prints() {
    let target = tempfile::tempdir().unwrap();
    let publish = |end: HarnessEnd, file: &[u8]| {
        let tests = harness_rows(
            HARNESS,
            &HarnessObservation { end: Ok(end), result_file: Ok(file.to_vec()) },
        );
        let view = crate::agent_delta::publish_shown(
            target.path(),
            &[("fixture".to_string(), record_bytes(&[], &tests))],
            &crate::agent_delta::DeltaRequest::default(),
            Some("agent"),
            false,
        );
        view.lines()
    };
    // The base failed `a` and passed `b`; now the harness crashes before
    // either reports. The failure still prints, not concluded `(was failed)`;
    // the pass is under the harness row alone. Neither is a changed case.
    publish(HarnessEnd::Exited { code: 101 }, b"failed a\nok b\n");
    let crashed = publish(HarnessEnd::Signaled { signal: 6 }, b"");
    assert_eq!(
        crashed[..2],
        [
            format!(
                "CHANGED     [TEST HARNESS not concluded]  {HARNESS}  harness  not concluded: \
                 ended by signal 6 (was concluded)  reported by its harness  -"
            ),
            format!(
                "STILL       [TEST not concluded]  {HARNESS}::a  test  not concluded (was \
                 failed)  reported by its harness  -"
            ),
        ]
    );
    assert_eq!(crashed.len(), 3, "{crashed:#?}");
    assert!(crashed[2].contains("; 0 of 0 test case(s) changed"), "{}", crashed[2]);
    // Against a base where `a` passed, its absence is the harness row's alone.
    publish(HarnessEnd::Exited { code: 0 }, b"ok a\n");
    let crashed = publish(HarnessEnd::Signaled { signal: 6 }, b"");
    assert_eq!(crashed.len(), 2, "{crashed:#?}");
}

/// A harness can replace either known result path with a FIFO before exiting.
/// Observation happens after execution, so it must refuse without a writer.
#[test]
fn fifo_observation_child() {
    let Some(root) = std::env::var_os("TARGO_RESULT_FIFO_OBSERVATION") else { return };
    let files = HarnessResultFiles::for_harness(&Path::new(&root).join("plan.json"), 0).unwrap();
    let observed = observe(&files, identity(&executable()));
    let rows = harness_rows(HARNESS, &observed);
    assert!(!rows.harnesses[0].concluded, "{rows:?}");
    assert!(rows.harnesses[0].reason.as_ref().unwrap().contains("not a regular file"));
    assert!(rows.cases.iter().all(|case| case.outcome == CaseOutcome::NotConcluded));
}

#[test]
fn fifo_result_paths_cannot_block_observation_after_a_harness_exits() {
    use std::os::unix::ffi::OsStrExt;
    use std::time::{Duration, Instant};
    for exit_fifo in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let files = HarnessResultFiles::for_harness(&dir.path().join("plan.json"), 0).unwrap();
        std::fs::create_dir_all(Path::new(&files.logfile).parent().unwrap()).unwrap();
        let fifo = if exit_fifo {
            std::fs::write(&files.logfile, b"ok completed_case\n").unwrap();
            &files.exit
        } else {
            write_exit(
                Path::new(&files.exit),
                &exit_record(&files, HarnessEnd::Exited { code: 0 }),
            )
            .unwrap();
            &files.logfile
        };
        let name = std::ffi::CString::new(Path::new(fifo).as_os_str().as_bytes()).unwrap();
        assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
        let mut child = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "test_results::tests::fifo_observation_child", "--nocapture"])
            .env("TARGO_RESULT_FIFO_OBSERVATION", dir.path())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(5);
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if Instant::now() >= deadline {
                child.kill().unwrap();
                child.wait().unwrap();
                panic!("observation blocked on a FIFO with no writer (exit_fifo={exit_fifo})");
            }
            std::thread::sleep(Duration::from_millis(10));
        };
        assert!(status.success(), "observation child failed (exit_fifo={exit_fifo}): {status}");
    }
}
