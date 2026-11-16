// targo-trust/test_results.rs: each test case's outcome as a record row
// (live-edit-loop plan, step 2 DELTA; docs/design/2026-11-12-live-edit-loop.md).
//
// THE CHANNEL. `targo trust test` executes the prepared harnesses through
// native Targo after the frontend gate. A test binary's stdout and stderr are
// the tests' own: user code writes to them as freely as libtest does, so this
// module never reads them. Native Targo gives each harness of the sealed plan
// its own libtest result file (`--logfile <file>`, the first two arguments of
// that harness's plan entry, authenticated with the rest of the plan, so no
// test argument after it, `--` or a value-taking `--skip`, can swallow it)
// and, after the harness process ends, an exit record beside it saying how it
// ended (`trust_test_execution::results`). This module reads both.
//
// Why `--logfile`: it is stable libtest (deprecated upstream, so a harness
// prints one warning on stderr, and still accepted), it writes one line per
// finished case apart from the output streams, and a test binary that
// refuses an unknown option exits 101 with no failed case, which reads as not
// concluded below. Libtest's JSON event format would add a case count, but it
// needs `-Z unstable-options`; a channel that a stable test binary may refuse
// is not one to build on.
//
// AUTHORITY. An outcome here is what the test binary's own harness reported.
// The harness is linked into the user's program and the user's code can
// write the result file as freely as libtest does, so a row is never proof:
// it raises no verdict, enters no gate, count or vector, and its rows never
// print a proof word. These rows never select an exit status. Native Targo
// observes the harnesses' exit statuses; result-channel setup or exit-record
// write failure can additionally refuse the command. An unreadable result
// file instead produces not-concluded rows, without promoting a verdict.
//
// FAIL CLOSED. A harness CONCLUDED when native Targo recorded that its process
// exited with status 0 and its result file reports no failed case, or exited
// with libtest's failure status 101 and the file reports at least one failed
// case; the file is complete (empty, or ending in a newline), UTF-8, every
// line is a libtest result line and no case is reported twice; and the exit
// record names this session, this executable, its bytes and this result file.
// Anything else is NOT CONCLUDED with its reason: a signal (an abort, a kill,
// the run's timeout), another status, no exit record, a missing, truncated or
// unreadable result file, or a file that disagrees with the exit status. In a
// harness that did not conclude a case the file reports failed stays failed
// (a failure is never shown less), also one reported after a line that is not
// a result line (reading goes on past such a line) or reported again
// otherwise, and every other case it reports is not concluded: a case is
// never `passed` from a harness that did not conclude. An unfinished last line
// is not read, since its name may be cut short; it leaves the harness not
// concluded. A harness that native Targo was never asked to record (a native
// companion built before the channel, or execution refused before it
// started) is not concluded, with no case rows.
//
// What a conclusion cannot see: the result file has no inventory of cases, so
// a test that ends its own process with status 0 (or 101 after a failure) hides
// the cases that had not run yet. Against a base they are `VANISHED` rows,
// which print.
//
// Which cases run is the harnesses' arguments' choice (a filter, `--exact`,
// `--ignored`), so the record names them ([`harness_arguments`]) and a test
// run's base is only a test run given the same ones (`crate::agent_delta`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use trust_test_execution::results::{
    HARNESS_EXIT_SCHEMA, HarnessEnd, HarnessResultFiles, MAX_LOGFILE_BYTES, read_bounded, read_exit,
};

/// Libtest's exit status when a test failed.
pub(crate) const LIBTEST_FAILED_STATUS: i32 = 101;

/// What a case's harness reported about it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CaseOutcome {
    Passed,
    Failed,
    Ignored,
    NotConcluded,
}

impl CaseOutcome {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Passed => "passed",
            Self::Failed => "failed",
            Self::Ignored => "ignored",
            Self::NotConcluded => "not concluded",
        }
    }

    pub(crate) fn parse(text: &str) -> Option<Self> {
        [Self::Passed, Self::Failed, Self::Ignored, Self::NotConcluded]
            .into_iter()
            .find(|outcome| outcome.as_str() == text)
    }
}

/// One case: `<harness key>::<case name>` and its outcome.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct TestCaseRecord {
    pub(crate) key: String,
    pub(crate) outcome: CaseOutcome,
}

impl TestCaseRecord {
    /// The harness key of the case: everything before its first `::`.
    pub(crate) fn harness(&self) -> &str {
        self.key.split_once("::").map_or(self.key.as_str(), |(harness, _)| harness)
    }
}

/// One harness: `<kinds>/<target name>`, whether it concluded, and why not.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct TestHarnessRecord {
    pub(crate) key: String,
    pub(crate) concluded: bool,
    /// Why it did not conclude; `None` when it did.
    pub(crate) reason: Option<String>,
}

/// The test rows of one package's record.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct PackageTests {
    pub(crate) harnesses: Vec<TestHarnessRecord>,
    pub(crate) cases: Vec<TestCaseRecord>,
}

impl PackageTests {
    fn sort(&mut self) {
        self.harnesses.sort();
        self.cases.sort();
    }
}

/// The key of a harness: its target kinds and name, `test/agent_delta`.
pub(crate) fn harness_key(kinds: &[String], target_name: &str) -> String {
    format!("{}/{target_name}", kinds.join(","))
}

/// A libtest result line's word.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reported {
    Ok,
    Failed,
    Ignored,
}

/// The cases a result file reports, in file order, and the first problem
/// found, if any. A problem does not stop reading: every later record is
/// still read, so a failure the file reports after a line that is not a
/// result line keeps its `failed` row (the problem leaves the harness not
/// concluded, so no other case of it is `passed`). An unfinished last line is
/// not a record and is not read: its name may be cut short.
#[derive(Debug, Default)]
struct Parsed {
    cases: Vec<(Reported, String)>,
    problem: Option<String>,
}

/// Libtest's result words (`library/test/src/console.rs`,
/// `write_log_result`), longest first: (prefix, word, takes a message).
const RESULT_WORDS: [(&str, Reported, bool); 6] = [
    ("ok ", Reported::Ok, false),
    ("failed (time limit exceeded) ", Reported::Failed, false),
    ("failed: ", Reported::Failed, true),
    ("failed ", Reported::Failed, false),
    ("ignored: ", Reported::Ignored, true),
    ("ignored ", Reported::Ignored, false),
];

/// `<word> <name>`, `<word>: <message> <name>` (the message may run over
/// lines), each record optionally ending in ` <exec time>`. The name is the
/// record's last whitespace-free token.
fn parse_result_file(bytes: &[u8]) -> Parsed {
    let mut parsed = Parsed::default();
    let Ok(text) = std::str::from_utf8(bytes) else {
        parsed.problem = Some("the result file is not UTF-8".into());
        return parsed;
    };
    let (complete, truncated) = match text.rfind('\n') {
        Some(end) => (&text[..=end], end + 1 < text.len()),
        None => ("", !text.is_empty()),
    };
    let note = |parsed: &mut Parsed, problem: String| {
        parsed.problem.get_or_insert(problem);
    };
    // (word, takes a message, the record's last line)
    let mut open: Option<(Reported, bool, &str)> = None;
    let close = |open: &mut Option<(Reported, bool, &str)>, parsed: &mut Parsed| {
        let Some((word, _, last)) = open.take() else { return true };
        let last = match last.rfind(" <") {
            Some(at) if last.ends_with('>') => &last[..at],
            _ => last,
        };
        match last.rsplit(char::is_whitespace).next().filter(|name| !name.is_empty()) {
            Some(name) => {
                parsed.cases.push((word, name.to_string()));
                true
            }
            None => false,
        }
    };
    for (index, line) in complete.lines().enumerate() {
        let number = index + 1;
        match RESULT_WORDS.into_iter().find(|(prefix, _, _)| line.starts_with(prefix)) {
            Some((prefix, word, message)) => {
                if !close(&mut open, &mut parsed) {
                    note(
                        &mut parsed,
                        format!("the record before result line {number} names no case"),
                    );
                }
                let rest = &line[prefix.len()..];
                if !message && rest.trim_end().contains(char::is_whitespace) {
                    // `<word> <name> <time>` is the only plain record with a
                    // space. Another shape is a problem, and the record is
                    // still read by its last token: a `failed` line keeps
                    // its failure.
                    let timed = rest.rfind(" <").is_some_and(|at| {
                        rest.ends_with('>') && !rest[..at].contains(char::is_whitespace)
                    });
                    if !timed {
                        note(
                            &mut parsed,
                            format!("result line {number} is not a libtest result line"),
                        );
                    }
                }
                open = Some((word, message, line));
            }
            None => match &mut open {
                Some((_, true, last)) => *last = line,
                // A plain record stays open; it names its case on its own line.
                _ => {
                    note(&mut parsed, format!("result line {number} is not a libtest result line"))
                }
            },
        }
    }
    if !close(&mut open, &mut parsed) {
        note(&mut parsed, "the last result line names no case".into());
    }
    if truncated {
        note(&mut parsed, "the result file ends in an unfinished line (truncated)".into());
    }
    parsed
}

/// What native Targo left for one harness, read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct HarnessObservation {
    /// How the process ended, or why that is not known.
    pub(crate) end: Result<HarnessEnd, String>,
    /// The result file's bytes, or why they could not be read.
    pub(crate) result_file: Result<Vec<u8>, String>,
}

/// The identity a harness's exit record must name.
#[derive(Debug, Clone, Copy)]
pub(crate) struct HarnessIdentity<'a> {
    pub(crate) session: &'a str,
    pub(crate) executable: &'a str,
    pub(crate) sha256: &'a str,
}

/// Read a harness's exit record and result file. Neither path is in a reason:
/// reasons are in the record, and the record must not change with the
/// session directory.
pub(crate) fn observe(
    files: &HarnessResultFiles,
    identity: HarnessIdentity<'_>,
) -> HarnessObservation {
    let end = read_exit(Path::new(&files.exit))
        .map_err(|error| format!("no exit record ({error})"))
        .and_then(|exit| {
            if exit.schema == HARNESS_EXIT_SCHEMA
                && exit.session == identity.session
                && exit.executable == identity.executable
                && exit.sha256 == identity.sha256
                && exit.logfile == files.logfile
            {
                Ok(exit.end)
            } else {
                Err("the exit record names another harness".to_string())
            }
        });
    let result_file = read_bounded(Path::new(&files.logfile), MAX_LOGFILE_BYTES)
        .map_err(|error| format!("no readable result file ({error})"));
    HarnessObservation { end, result_file }
}

/// The rows of one harness keyed `harness`, from what was observed (module
/// docs, FAIL CLOSED).
pub(crate) fn harness_rows(harness: &str, observed: &HarnessObservation) -> PackageTests {
    let parsed = match &observed.result_file {
        Ok(bytes) => parse_result_file(bytes),
        Err(error) => Parsed { cases: Vec::new(), problem: Some(error.clone()) },
    };
    let mut names: BTreeSet<&str> = BTreeSet::new();
    let repeated = parsed.cases.iter().find(|(_, name)| !names.insert(name)).map(|(_, n)| n);
    let any_failed = parsed.cases.iter().any(|(word, _)| *word == Reported::Failed);
    let reason = match &observed.end {
        Err(error) => Some(error.clone()),
        Ok(HarnessEnd::NotObserved { reason }) => Some(format!("no exit was observed: {reason}")),
        Ok(HarnessEnd::Signaled { signal }) => Some(format!("ended by signal {signal}")),
        Ok(HarnessEnd::Exited { code }) => {
            if let Some(problem) = &parsed.problem {
                Some(format!("exited with status {code}, but {problem}"))
            } else if let Some(name) = repeated {
                Some(format!(
                    "exited with status {code}, but its result file reports `{name}` twice"
                ))
            } else if *code == 0 && any_failed {
                Some("exited with status 0, but its result file reports a failed case".into())
            } else if *code == LIBTEST_FAILED_STATUS && !any_failed {
                Some(format!(
                    "exited with status {LIBTEST_FAILED_STATUS}, but its result file reports no \
                     failed case"
                ))
            } else if *code != 0 && *code != LIBTEST_FAILED_STATUS {
                Some(format!("exited with status {code}"))
            } else {
                None
            }
        }
    };
    let concluded = reason.is_none();
    // One row per case name, in first-reported order. A name the file reports
    // more than once (which already leaves the harness not concluded) is
    // `failed` when any of its lines is: a failure is never shown less, so a
    // forged `ok` line ahead of a case's real `failed` line cannot hide it.
    let mut order: Vec<&str> = Vec::new();
    let mut words: BTreeMap<&str, Reported> = BTreeMap::new();
    for (word, name) in &parsed.cases {
        match words.get_mut(name.as_str()) {
            None => {
                order.push(name);
                words.insert(name, *word);
            }
            Some(kept) if *word == Reported::Failed => *kept = Reported::Failed,
            Some(_) => {}
        }
    }
    let cases = order
        .into_iter()
        .map(|name| TestCaseRecord {
            key: format!("{harness}::{name}"),
            outcome: match (words[name], concluded) {
                (Reported::Failed, _) => CaseOutcome::Failed,
                (_, false) => CaseOutcome::NotConcluded,
                (Reported::Ok, true) => CaseOutcome::Passed,
                (Reported::Ignored, true) => CaseOutcome::Ignored,
            },
        })
        .collect();
    let mut tests = PackageTests {
        harnesses: vec![TestHarnessRecord { key: harness.to_string(), concluded, reason }],
        cases,
    };
    tests.sort();
    tests
}

/// A harness the run authorized, as the result reader needs it.
#[derive(Debug, Clone)]
pub(crate) struct AuthorizedHarness {
    pub(crate) package: String,
    pub(crate) key: String,
    /// The canonical executable path, as the plan names it.
    pub(crate) executable: String,
}

/// How far execution got.
#[derive(Debug, Clone)]
pub(crate) enum Execution<'a> {
    /// Native Targo ran this authenticated plan.
    Ran { session: &'a str, plan: &'a trust_test_execution::PreparedTests },
    /// No harness was started, for this reason.
    NotRun(String),
}

/// The libtest arguments the harnesses of an executed `plan` were given,
/// without the result channel: Cargo gives every harness the same ones, so
/// they are one harness's; were they ever to differ, every harness's in plan
/// order. They choose which cases run (a filter, `--exact`, `--ignored`), so
/// a record names them and is compared only with a record given the same.
pub(crate) fn harness_arguments(plan: &trust_test_execution::PreparedTests) -> Vec<String> {
    let mut each: Vec<&[String]> = plan
        .tests
        .iter()
        .map(|test| match &test.results {
            // The plan's validation puts the channel's two arguments first.
            Some(_) => test.args.get(2..).unwrap_or_default(),
            None => test.args.as_slice(),
        })
        .collect();
    each.dedup();
    each.concat()
}

/// Every authorized harness's rows, by package. A harness with no plan entry,
/// or whose plan entry names no result files, is not concluded.
pub(crate) fn collect(
    harnesses: &[AuthorizedHarness],
    execution: Execution<'_>,
) -> BTreeMap<String, PackageTests> {
    let mut packages: BTreeMap<String, PackageTests> = BTreeMap::new();
    for harness in harnesses {
        let not_concluded = |reason: String| PackageTests {
            harnesses: vec![TestHarnessRecord {
                key: harness.key.clone(),
                concluded: false,
                reason: Some(reason),
            }],
            cases: Vec::new(),
        };
        let rows = match &execution {
            Execution::NotRun(reason) => not_concluded(format!("not run: {reason}")),
            Execution::Ran { session, plan } => {
                match plan.tests.iter().find(|test| test.executable == harness.executable) {
                    None => not_concluded("the executed plan has no entry for this harness".into()),
                    Some(test) => match &test.results {
                        None => not_concluded(
                            "this native Targo records no per-case results (a companion built \
                             before the result channel)"
                                .into(),
                        ),
                        Some(files) => harness_rows(
                            &harness.key,
                            &observe(
                                files,
                                HarnessIdentity {
                                    session,
                                    executable: &test.executable,
                                    sha256: &test.sha256,
                                },
                            ),
                        ),
                    },
                }
            }
        };
        let entry = packages.entry(harness.package.clone()).or_default();
        entry.harnesses.extend(rows.harnesses);
        entry.cases.extend(rows.cases);
    }
    for tests in packages.values_mut() {
        tests.sort();
    }
    packages
}

#[cfg(all(test, unix))]
#[path = "test_results_tests.rs"]
mod tests;
