//! This module renders the JSON output of libtest into a human-readable form, trying to be as
//! similar to libtest's native output as possible.
//!
//! This is needed because we need to use libtest in JSON mode to extract granular information
//! about the executed tests. Doing so suppresses the human-readable output, and (compared to Cargo
//! and rustc) libtest doesn't include the rendered human-readable output as a JSON field. We had
//! to reimplement all the rendering logic in this module because of that.

use std::collections::HashSet;
use std::env;
use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

use termcolor::{Color, ColorSpec, WriteColor};

use crate::core::build_steps::test::failed_tests::RecordFailedTests;
use crate::core::builder::Builder;
use crate::utils::exec::{BootstrapCommand, CommandReader};
use crate::utils::helpers;

const TERSE_TESTS_PER_LINE: usize = 88;
// Trust: keep compiletest's structured case evidence separate from rendered output.
const CASE_EVENT_SCHEMA: &str = "trust.compiletest.case-events/v1";
static NEXT_CASE_STREAM: AtomicU64 = AtomicU64::new(0);

pub(crate) fn add_flags_and_try_run_tests(
    builder: &Builder<'_>,
    cmd: &mut BootstrapCommand,
    record_failed_tests: RecordFailedTests,
) -> bool {
    add_flags_and_try_run_tests_with_postcheck(builder, cmd, record_failed_tests, || Ok(()))
}

// Trust: retained test inputs must be checked even when a test failed and the
// ordinary failure policy will exit immediately afterward.
pub(crate) fn add_flags_and_try_run_tests_with_postcheck(
    builder: &Builder<'_>,
    cmd: &mut BootstrapCommand,
    record_failed_tests: RecordFailedTests,
    postcheck: impl FnOnce() -> Result<(), String>,
) -> bool {
    if !cmd.get_args().any(|arg| arg == "--") {
        cmd.arg("--");
    }
    cmd.args(["-Z", "unstable-options", "--format", "json"]);

    try_run_tests_with_postcheck(builder, cmd, false, record_failed_tests, postcheck)
}

pub(crate) fn try_run_tests(
    builder: &Builder<'_>,
    cmd: &mut BootstrapCommand,
    stream: bool,
    record_failed_tests: RecordFailedTests,
) -> bool {
    try_run_tests_with_postcheck(builder, cmd, stream, record_failed_tests, || Ok(()))
}

fn completed_test_and_postcheck(
    run: impl FnOnce() -> bool,
    postcheck: impl FnOnce() -> Result<(), String>,
) -> (bool, Option<String>) {
    let tests_passed = run();
    let input_error = postcheck().err();
    (tests_passed && input_error.is_none(), input_error)
}

fn try_run_tests_with_postcheck(
    builder: &Builder<'_>,
    cmd: &mut BootstrapCommand,
    stream: bool,
    record_failed_tests: RecordFailedTests,
    postcheck: impl FnOnce() -> Result<(), String>,
) -> bool {
    let (passed, input_error) = completed_test_and_postcheck(
        || run_tests(builder, cmd, stream, record_failed_tests),
        postcheck,
    );
    if let Some(error) = &input_error {
        eprintln!("test input validation failed: {error}");
    }
    if passed {
        return true;
    }

    if builder.fail_fast {
        helpers::exit_process(1);
    }

    let message = match input_error {
        Some(error) => format!("{cmd:?}; input error: {error}"),
        None => format!("{cmd:?}"),
    };
    builder.config.exec_ctx().add_to_delay_failure(message);

    false
}

fn run_tests(
    builder: &Builder<'_>,
    cmd: &mut BootstrapCommand,
    stream: bool,
    record_failed_tests: RecordFailedTests,
) -> bool {
    builder.do_if_verbose(|| println!("running: {cmd:?}"));

    let Some(mut streaming_command) = cmd.stream_capture_stdout(&builder.config.exec_ctx) else {
        return true;
    };

    let (case_events, sidecar_error) = match CaseEventForwarder::for_command(cmd) {
        Ok(events) => (events, None),
        Err(error) => (None, Some(error)),
    };
    // This runs until the stdout of the child is closed, which means the child exited. We don't
    // run this on another thread since the builder is not Sync.
    let renderer = Renderer::new(
        streaming_command.stdout.take().unwrap(),
        builder,
        record_failed_tests,
        case_events,
    );
    let render_result = if stream {
        renderer.stream_all();
        validate_raw_stream_mode(cmd)
    } else {
        renderer.render_all()
    };

    let status = streaming_command.wait(&builder.config.exec_ctx).unwrap();
    if !status.success() && builder.is_verbose() {
        println!(
            "\n\ncommand did not execute successfully: {cmd:?}\n\
             expected success, got: {status}",
        );
    }

    if let Some(error) = sidecar_error.or_else(|| render_result.err()) {
        eprintln!("compiletest case event sidecar failed: {error}");
        return false;
    }

    status.success()
}

// Trust: raw streaming must not bypass compiletest's structured case-event checks.
fn is_compiletest_command(cmd: &BootstrapCommand) -> bool {
    cmd.get_args().any(|arg| arg == "--suite")
}

fn validate_raw_stream_mode(cmd: &BootstrapCommand) -> Result<(), String> {
    if is_compiletest_command(cmd) {
        Err("compiletest --suite cannot bypass structured case event validation".to_owned())
    } else {
        Ok(())
    }
}

// Trust: the proof runner supplies this directory; each invocation gets its own JSONL stream.
struct CaseEventForwarder<W: Write> {
    writer: W,
    selected: Option<usize>,
    started: HashSet<String>,
    terminal: HashSet<String>,
    passed: usize,
    failed: usize,
    ignored: usize,
    saw_suite_end: bool,
    error: Option<String>,
}

impl CaseEventForwarder<File> {
    fn for_command(cmd: &BootstrapCommand) -> Result<Option<Self>, String> {
        let Some(proof_dir) = env::var_os("TRUST_UPSTREAM_RUST_PROOF_DIR") else {
            return Ok(None);
        };
        if !is_compiletest_command(cmd) {
            return Ok(None);
        }

        let args = cmd
            .get_args()
            .map(|arg| {
                arg.to_str()
                    .map(str::to_owned)
                    .ok_or_else(|| "non-UTF-8 compiletest argument".to_owned())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let proof_dir = PathBuf::from(proof_dir);
        Self::create(&proof_dir, args).map(Some)
    }

    fn create(proof_dir: &Path, args: Vec<String>) -> Result<Self, String> {
        let mut file = loop {
            let serial = NEXT_CASE_STREAM.fetch_add(1, Ordering::Relaxed);
            let path =
                proof_dir.join(format!("compiletest-events-{}-{serial}.jsonl", std::process::id()));
            match OpenOptions::new().write(true).create_new(true).open(&path) {
                Ok(file) => break file,
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(format!("cannot create {}: {error}", path.display())),
            }
        };
        let header = serde_json::json!({
            "schema": CASE_EVENT_SCHEMA,
            "type": "invocation",
            "argv": args,
        });
        writeln!(file, "{header}").map_err(|error| format!("cannot write sidecar: {error}"))?;
        Ok(Self::new(file))
    }
}

impl<W: Write> CaseEventForwarder<W> {
    fn new(writer: W) -> Self {
        Self {
            writer,
            selected: None,
            started: HashSet::new(),
            terminal: HashSet::new(),
            passed: 0,
            failed: 0,
            ignored: 0,
            saw_suite_end: false,
            error: None,
        }
    }

    fn active(&self) -> bool {
        self.selected.is_some()
    }

    fn reject(&mut self, reason: &str) {
        if self.error.is_none() {
            self.error = Some(reason.to_owned());
        }
    }

    fn forward_parsed(&mut self, line: &[u8], is_case_event: bool, message: &Message) {
        if is_case_event {
            self.record(line, message);
        } else {
            self.reject("untagged or unknown compiletest event");
        }
    }

    fn record(&mut self, line: &[u8], message: &Message) {
        if let Err(error) = self.writer.write_all(line) {
            self.reject(&format!("cannot write case event: {error}"));
        }
        match message {
            Message::Suite(SuiteMessage::Started { test_count, selected_count }) => {
                if self.selected.replace(*test_count).is_some() {
                    self.reject("duplicate compiletest suite start");
                }
                if *test_count == 0 || *selected_count != Some(*test_count) {
                    self.reject("empty or inconsistent compiletest selection");
                }
            }
            Message::Test(TestMessage::Started { name }) => {
                if let Some(name) = name {
                    if self.selected.is_none() || self.saw_suite_end {
                        self.reject("test start outside compiletest suite");
                    }
                    if !self.started.insert(name.clone()) {
                        self.reject("duplicate selected test identity");
                    }
                } else {
                    self.reject("test start missing identity");
                }
            }
            Message::Test(TestMessage::Ok(outcome)) => {
                self.passed += 1;
                self.record_terminal(&outcome.name);
            }
            Message::Test(TestMessage::Failed(outcome)) => {
                self.failed += 1;
                self.record_terminal(&outcome.name);
            }
            Message::Test(TestMessage::Ignored(outcome)) => {
                self.ignored += 1;
                self.record_terminal(&outcome.name);
            }
            Message::Test(TestMessage::Timeout { name }) => {
                if !self.started.contains(name) || self.saw_suite_end {
                    self.reject("timeout outside started test");
                }
            }
            Message::Suite(SuiteMessage::Ok(outcome)) => self.record_suite_end(outcome, true),
            Message::Suite(SuiteMessage::Failed(outcome)) => {
                self.record_suite_end(outcome, false);
            }
            Message::Bench(_) | Message::Report(_) => {
                self.reject("unexpected compiletest case event");
            }
        }
    }

    fn record_terminal(&mut self, name: &str) {
        if self.selected.is_none() || self.saw_suite_end || !self.started.contains(name) {
            self.reject("terminal event outside started test");
        }
        if !self.terminal.insert(name.to_owned()) {
            self.reject("duplicate terminal event");
        }
    }

    fn record_suite_end(&mut self, outcome: &SuiteOutcome, event_ok: bool) {
        if self.saw_suite_end || self.selected.is_none() {
            self.reject("suite end without unique start");
        }
        self.saw_suite_end = true;
        let selected = self.selected.unwrap_or(0);
        let executed = self.passed + self.failed;
        let terminal = executed + self.ignored;
        if outcome.selected_count != Some(selected)
            || outcome.executed_count != Some(executed)
            || outcome.terminal_count != Some(terminal)
            || outcome.passed != self.passed
            || outcome.failed != self.failed
            || outcome.ignored != self.ignored
            || outcome.protocol_valid != Some(true)
            || selected == 0
            || self.started.len() != selected
            || self.terminal.len() != selected
            || terminal != selected
            || event_ok != (self.failed == 0)
        {
            self.reject("inconsistent or incomplete compiletest suite");
        }
    }

    fn finish(mut self) -> Result<(), String> {
        if self.selected.is_none() || !self.saw_suite_end {
            self.reject("missing complete compiletest case stream");
        }
        if let Err(error) = self.writer.flush() {
            self.reject(&format!("cannot flush case events: {error}"));
        }
        self.error.map_or(Ok(()), Err)
    }

    // Trust: a reused native execution success requires real, successful cases.
    // The ordinary sidecar still faithfully records failed and ignored suites.
    fn finish_executed(self) -> Result<(), String> {
        if self.passed == 0 || self.failed != 0 || self.ignored != 0 {
            return Err(
                "native repository UI selection did not execute every case successfully".into()
            );
        }
        self.finish()
    }
}

struct Renderer<'a> {
    stdout: BufReader<CommandReader>,
    failures: Vec<TestOutcome>,
    benches: Vec<BenchOutcome>,
    builder: &'a Builder<'a>,
    tests_count: Option<usize>,
    executed_tests: usize,
    /// Number of tests that were skipped due to already being up-to-date
    /// (i.e. no relevant changes occurred since they last ran).
    up_to_date_tests: usize,
    ignored_tests: usize,
    terse_tests_in_line: usize,
    ci_latest_logged_percentage: f64,

    failed_tests: Option<File>,
    case_events: Option<CaseEventForwarder<File>>,
    // Trust: validate native workflow cases in memory, without another report artifact.
    native_cases: Option<CaseEventForwarder<std::io::Sink>>,
}

impl<'a> Renderer<'a> {
    fn new(
        stdout: CommandReader,
        builder: &'a Builder<'a>,
        record_failed_tests: RecordFailedTests,
        case_events: Option<CaseEventForwarder<File>>,
    ) -> Self {
        let failed_tests = record_failed_tests.path().and_then(|path| {
            // create the file (overwriting any previous) to get ready to record new failed tests
            match File::options().create(true).append(true).truncate(false).open(path) {
                Ok(f) => Some(f),
                Err(e) => {
                    println!(
                        "Couldn't open file {} to write test failures to: {e}. (attempted because `--record` was passed). Test failures will not be recorded.",
                        path.display()
                    );
                    None
                }
            }
        });

        Self {
            stdout: BufReader::new(stdout),
            benches: Vec::new(),
            failures: Vec::new(),
            builder,
            tests_count: None,
            executed_tests: 0,
            up_to_date_tests: 0,
            ignored_tests: 0,
            terse_tests_in_line: 0,
            ci_latest_logged_percentage: 0.0,
            failed_tests,
            case_events,
            native_cases: builder
                .config
                .cmd
                .trust_repo_check()
                .then(|| CaseEventForwarder::new(std::io::sink())),
        }
    }

    fn render_all(mut self) -> Result<(), String> {
        let mut line = Vec::new();
        loop {
            line.clear();
            match self.stdout.read_until(b'\n', &mut line) {
                Ok(_) => {}
                Err(err) if err.kind() == std::io::ErrorKind::UnexpectedEof => break,
                Err(err) => panic!("failed to read output of test runner: {err}"),
            }
            if line.is_empty() {
                break;
            }

            match serde_json::from_slice::<serde_json::Value>(&line) {
                Ok(value) => {
                    let schema = value.get("schema").and_then(serde_json::Value::as_str);
                    let is_case_event = schema == Some(CASE_EVENT_SCHEMA);
                    let unknown_case_event =
                        schema.is_some_and(|s| s.starts_with("trust.compiletest."));
                    match serde_json::from_value::<Message>(value) {
                        Ok(parsed) => {
                            if let Some(events) = &mut self.case_events {
                                events.forward_parsed(&line, is_case_event, &parsed);
                            }
                            if let Some(events) = &mut self.native_cases {
                                events.forward_parsed(&line, is_case_event, &parsed);
                            }
                            self.render_message(parsed);
                        }
                        Err(_) => {
                            if let Some(events) = &mut self.case_events
                                && (unknown_case_event || events.active())
                            {
                                events.reject("invalid compiletest event JSON");
                            }
                            if let Some(events) = &mut self.native_cases
                                && (unknown_case_event || events.active())
                            {
                                events.reject("invalid compiletest event JSON");
                            }
                            let mut stdout = std::io::stdout();
                            stdout.write_all(&line).unwrap();
                            let _ = stdout.flush();
                        }
                    }
                }
                Err(_err) => {
                    // Handle non-JSON output, for example when --nocapture is passed.
                    if let Some(events) = &mut self.case_events
                        && events.active()
                    {
                        events.reject("non-JSON output in compiletest event stream");
                    }
                    if let Some(events) = &mut self.native_cases
                        && events.active()
                    {
                        events.reject("non-JSON output in compiletest event stream");
                    }
                    let mut stdout = std::io::stdout();
                    stdout.write_all(&line).unwrap();
                    let _ = stdout.flush();
                }
            }
        }

        if self.up_to_date_tests > 0 {
            let n = self.up_to_date_tests;
            let s = if n > 1 { "s" } else { "" };
            println!("help: ignored {n} up-to-date test{s}; use `--force-rerun` to prevent this\n");
        }

        if let Some(events) = self.native_cases {
            events.finish_executed()?;
        }
        match self.case_events {
            Some(events) => events.finish(),
            None => Ok(()),
        }
    }

    /// Renders the stdout characters one by one
    fn stream_all(mut self) {
        let mut buffer = [0; 1];
        loop {
            match self.stdout.read(&mut buffer) {
                Ok(0) => break,
                Ok(_) => {
                    let mut stdout = std::io::stdout();
                    stdout.write_all(&buffer).unwrap();
                    let _ = stdout.flush();
                }
                Err(err) if err.kind() == std::io::ErrorKind::UnexpectedEof => break,
                Err(err) => panic!("failed to read output of test runner: {err}"),
            }
        }
    }

    fn render_test_outcome(&mut self, outcome: Outcome<'_>, test: &TestOutcome) {
        self.executed_tests += 1;

        if let Outcome::Ignored { reason } = outcome {
            self.ignored_tests += 1;
            // Keep this in sync with the "up-to-date" ignore message inserted by compiletest.
            if reason == Some("up-to-date") {
                self.up_to_date_tests += 1;
            }
        }

        #[cfg(feature = "build-metrics")]
        self.builder.metrics.record_test(
            &test.name,
            match outcome {
                Outcome::Ok | Outcome::BenchOk => build_helper::metrics::TestOutcome::Passed,
                Outcome::Failed => build_helper::metrics::TestOutcome::Failed,
                Outcome::Ignored { reason } => build_helper::metrics::TestOutcome::Ignored {
                    ignore_reason: reason.map(|s| s.to_string()),
                },
            },
            self.builder,
        );

        if self.builder.config.verbose_tests {
            self.render_test_outcome_verbose(outcome, test);
        } else if self.builder.config.is_running_on_ci() {
            self.render_test_outcome_ci(outcome, test);
        } else {
            self.render_test_outcome_terse(outcome, test);
        }
    }

    fn render_test_outcome_verbose(&self, outcome: Outcome<'_>, test: &TestOutcome) {
        print!("test {} ... ", test.name);
        self.builder.colored_stdout(|stdout| outcome.write_long(stdout)).unwrap();
        if let Some(exec_time) = test.exec_time {
            print!(" ({exec_time:.2?})");
        }
        println!();
    }

    fn render_test_outcome_terse(&mut self, outcome: Outcome<'_>, test: &TestOutcome) {
        if self.terse_tests_in_line != 0
            && self.terse_tests_in_line.is_multiple_of(TERSE_TESTS_PER_LINE)
        {
            if let Some(total) = self.tests_count {
                let total = total.to_string();
                let executed = format!("{:>width$}", self.executed_tests - 1, width = total.len());
                print!(" {executed}/{total}");
            }
            println!();
            self.terse_tests_in_line = 0;
        }

        self.terse_tests_in_line += 1;
        self.builder.colored_stdout(|stdout| outcome.write_short(stdout, &test.name)).unwrap();
        let _ = std::io::stdout().flush();
    }

    fn render_test_outcome_ci(&mut self, outcome: Outcome<'_>, test: &TestOutcome) {
        if let Some(total) = self.tests_count {
            let percent = self.executed_tests as f64 / total as f64;

            if self.ci_latest_logged_percentage + 0.10 < percent {
                let total = total.to_string();
                let executed = format!("{:>width$}", self.executed_tests, width = total.len());
                let pretty_percent = format!("{:.0}%", percent * 100.0);
                let passed_tests = self.executed_tests - (self.failures.len() + self.ignored_tests);
                println!(
                    "{:<4} -- {executed}/{total}, {:>total_indent$} passed, {} failed, {} ignored",
                    pretty_percent,
                    passed_tests,
                    self.failures.len(),
                    self.ignored_tests,
                    total_indent = total.len()
                );
                self.ci_latest_logged_percentage += 0.10;
            }
        }

        self.builder.colored_stdout(|stdout| outcome.write_ci(stdout, &test.name)).unwrap();
        let _ = std::io::stdout().flush();
    }

    fn render_suite_outcome(&self, outcome: Outcome<'_>, suite: &SuiteOutcome) {
        // The terse output doesn't end with a newline, so we need to add it ourselves.
        if !self.builder.config.verbose_tests {
            println!();
        }

        if !self.failures.is_empty() {
            println!("\nfailures:\n");
            for failure in &self.failures {
                if failure.stdout.is_some() || failure.message.is_some() {
                    println!("---- {} stdout ----", failure.name);
                    if let Some(stdout) = &failure.stdout {
                        // Captured test output normally ends with a newline,
                        // so only use `println!` if it doesn't.
                        print!("{stdout}");
                        if !stdout.ends_with('\n') {
                            println!("\n\\ (no newline at end of output)");
                        }
                    }
                    println!("---- {} stdout end ----", failure.name);
                    if let Some(message) = &failure.message {
                        println!("NOTE: {message}");
                    }
                }
            }

            println!("\nfailures:");
            for failure in &self.failures {
                println!("    {}", failure.name);
            }

            if self.failed_tests.is_some() {
                println!(
                    "This list of test failures was recorded.\nUse `x test --rerun` to retry just these {} failed tests.",
                    self.failures.len(),
                )
            }
        }

        if !self.benches.is_empty() {
            println!("\nbenchmarks:");

            let mut rows = Vec::new();
            for bench in &self.benches {
                rows.push((
                    &bench.name,
                    format!("{:.2?}ns/iter", bench.median),
                    format!("+/- {:.2?}", bench.deviation),
                ));
            }

            let max_0 = rows.iter().map(|r| r.0.len()).max().unwrap_or(0);
            let max_1 = rows.iter().map(|r| r.1.len()).max().unwrap_or(0);
            let max_2 = rows.iter().map(|r| r.2.len()).max().unwrap_or(0);
            for row in &rows {
                println!("    {:<max_0$} {:>max_1$} {:>max_2$}", row.0, row.1, row.2);
            }
        }

        print!("\ntest result: ");
        self.builder.colored_stdout(|stdout| outcome.write_long(stdout)).unwrap();
        println!(
            ". {} passed; {} failed; {} ignored; {} measured; {} filtered out{time}\n",
            suite.passed,
            suite.failed,
            suite.ignored,
            suite.measured,
            suite.filtered_out,
            time = match suite.exec_time {
                Some(t) => format!("; finished in {:.2?}", Duration::from_secs_f64(t)),
                None => String::new(),
            }
        );
    }

    fn render_report(&self, report: &Report) {
        let &Report { total_time, compilation_time } = report;
        // Should match `write_merged_doctest_times` in `library/test/src/formatters/pretty.rs`.
        println!(
            "all doctests ran in {total_time:.2}s; merged doctests compilation took {compilation_time:.2}s"
        );
    }

    fn render_message(&mut self, message: Message) {
        match message {
            Message::Suite(SuiteMessage::Started { test_count, .. }) => {
                println!("\nrunning {test_count} tests");
                self.benches = vec![];
                self.failures = vec![];
                self.ignored_tests = 0;
                self.executed_tests = 0;
                self.terse_tests_in_line = 0;
                self.tests_count = Some(test_count);
            }
            Message::Suite(SuiteMessage::Ok(outcome)) => {
                self.render_suite_outcome(Outcome::Ok, &outcome);
            }
            Message::Suite(SuiteMessage::Failed(outcome)) => {
                self.render_suite_outcome(Outcome::Failed, &outcome);
            }
            Message::Report(report) => {
                self.render_report(&report);
            }
            Message::Bench(outcome) => {
                // The formatting for benchmarks doesn't replicate 1:1 the formatting libtest
                // outputs, mostly because libtest's formatting is broken in terse mode, which is
                // the default used by our monorepo. We use a different formatting instead:
                // successful benchmarks are just showed as "benchmarked"/"b", and the details are
                // outputted at the bottom like failures.
                let fake_test_outcome = TestOutcome {
                    name: outcome.name.clone(),
                    exec_time: None,
                    stdout: None,
                    message: None,
                };
                self.render_test_outcome(Outcome::BenchOk, &fake_test_outcome);
                self.benches.push(outcome);
            }
            Message::Test(TestMessage::Ok(outcome)) => {
                self.render_test_outcome(Outcome::Ok, &outcome);
            }
            Message::Test(TestMessage::Ignored(outcome)) => {
                self.render_test_outcome(
                    Outcome::Ignored { reason: outcome.message.as_deref() },
                    &outcome,
                );
            }
            Message::Test(TestMessage::Failed(outcome)) => {
                self.render_test_outcome(Outcome::Failed, &outcome);
                if let Some(failed_tests) = &mut self.failed_tests
                    && let Err(e) = writeln!(failed_tests, "{}", outcome.name)
                {
                    eprintln!(
                        "failed to write test failure to file: {e} (attempted because `--record` was passed)"
                    );
                }
                self.failures.push(outcome);
            }
            Message::Test(TestMessage::Timeout { name }) => {
                println!("test {name} has been running for a long time");
            }
            Message::Test(TestMessage::Started { .. }) => {} // Not useful
        }
    }
}

enum Outcome<'a> {
    Ok,
    BenchOk,
    Failed,
    Ignored { reason: Option<&'a str> },
}

impl Outcome<'_> {
    fn write_short(&self, writer: &mut dyn WriteColor, name: &str) -> Result<(), std::io::Error> {
        match self {
            Outcome::Ok => {
                writer.set_color(ColorSpec::new().set_fg(Some(Color::Green)))?;
                write!(writer, ".")?;
            }
            Outcome::BenchOk => {
                writer.set_color(ColorSpec::new().set_fg(Some(Color::Cyan)))?;
                write!(writer, "b")?;
            }
            Outcome::Failed => {
                // Put failed tests on their own line and include the test name, so that it's faster
                // to see which test failed without having to wait for them all to run.
                writeln!(writer)?;
                writer.set_color(ColorSpec::new().set_fg(Some(Color::Red)))?;
                writeln!(writer, "{name} ... F")?;
            }
            Outcome::Ignored { .. } => {
                writer.set_color(ColorSpec::new().set_fg(Some(Color::Yellow)))?;
                write!(writer, "i")?;
            }
        }
        writer.reset()
    }

    fn write_long(&self, writer: &mut dyn WriteColor) -> Result<(), std::io::Error> {
        match self {
            Outcome::Ok => {
                writer.set_color(ColorSpec::new().set_fg(Some(Color::Green)))?;
                write!(writer, "ok")?;
            }
            Outcome::BenchOk => {
                writer.set_color(ColorSpec::new().set_fg(Some(Color::Cyan)))?;
                write!(writer, "benchmarked")?;
            }
            Outcome::Failed => {
                writer.set_color(ColorSpec::new().set_fg(Some(Color::Red)))?;
                write!(writer, "FAILED")?;
            }
            Outcome::Ignored { reason } => {
                writer.set_color(ColorSpec::new().set_fg(Some(Color::Yellow)))?;
                write!(writer, "ignored")?;
                if let Some(reason) = reason {
                    write!(writer, ", {reason}")?;
                }
            }
        }
        writer.reset()
    }

    fn write_ci(&self, writer: &mut dyn WriteColor, name: &str) -> Result<(), std::io::Error> {
        match self {
            Outcome::Ok | Outcome::BenchOk | Outcome::Ignored { .. } => {}
            Outcome::Failed => {
                writer.set_color(ColorSpec::new().set_fg(Some(Color::Red)))?;
                writeln!(writer, "   {name} ... FAILED")?;
            }
        }
        writer.reset()
    }
}

#[derive(serde_derive::Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
enum Message {
    Suite(SuiteMessage),
    Test(TestMessage),
    Bench(BenchOutcome),
    Report(Report),
}

#[derive(serde_derive::Deserialize)]
#[serde(tag = "event", rename_all = "snake_case")]
enum SuiteMessage {
    Ok(SuiteOutcome),
    Failed(SuiteOutcome),
    Started { test_count: usize, selected_count: Option<usize> },
}

#[derive(serde_derive::Deserialize)]
struct SuiteOutcome {
    selected_count: Option<usize>,
    executed_count: Option<usize>,
    terminal_count: Option<usize>,
    protocol_valid: Option<bool>,
    passed: usize,
    failed: usize,
    ignored: usize,
    measured: usize,
    filtered_out: usize,
    /// The time it took to execute this test suite, or `None` if time measurement was not possible
    /// (e.g. due to running on wasm).
    exec_time: Option<f64>,
}

#[derive(serde_derive::Deserialize)]
#[serde(tag = "event", rename_all = "snake_case")]
enum TestMessage {
    Ok(TestOutcome),
    Failed(TestOutcome),
    Ignored(TestOutcome),
    Timeout { name: String },
    Started { name: Option<String> },
}

#[derive(serde_derive::Deserialize)]
struct BenchOutcome {
    name: String,
    median: f64,
    deviation: f64,
}

#[derive(serde_derive::Deserialize)]
struct TestOutcome {
    name: String,
    exec_time: Option<f64>,
    stdout: Option<String>,
    message: Option<String>,
}

/// Emitted when running doctests.
#[derive(serde_derive::Deserialize)]
struct Report {
    total_time: f64,
    compilation_time: f64,
}

#[cfg(test)]
mod tests;
