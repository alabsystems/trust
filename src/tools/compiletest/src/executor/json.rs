//! Collects statistics and emits suite/test events as JSON messages, using
//! the same JSON format as libtest's JSON formatter.
//!
//! These messages are then parsed by bootstrap, which replaces them with
//! user-friendly terminal output.

use std::collections::HashSet;
use std::time::Instant;

use serde_json::json;

use crate::executor::{CollectedTest, TestCompletion, TestOutcome};

// Trust: bootstrap forwards these records unchanged as per-case execution evidence.
const CASE_EVENT_SCHEMA: &str = "trust.compiletest.case-events/v1";

pub(crate) struct Listener {
    suite_start: Option<Instant>,
    cases: CaseLedger,
    passed: usize,
    failed: usize,
    ignored: usize,
    filtered_out: usize,
}

impl Listener {
    pub(crate) fn new() -> Self {
        Self {
            suite_start: None,
            cases: CaseLedger::new(0),
            passed: 0,
            failed: 0,
            ignored: 0,
            filtered_out: 0,
        }
    }

    fn print_message(&self, message: &serde_json::Value) {
        println!("{message}");
    }

    fn now(&self) -> Instant {
        Instant::now()
    }

    pub(crate) fn suite_started(&mut self, test_count: usize, filtered_out: usize) {
        self.suite_start = Some(self.now());
        self.cases = CaseLedger::new(test_count);
        self.filtered_out = filtered_out;
        let message = json!({
            "schema": CASE_EVENT_SCHEMA,
            "type": "suite",
            "event": "started",
            "test_count": test_count,
            "selected_count": test_count,
        });
        self.print_message(&message);
    }

    pub(crate) fn test_started(&mut self, test: &CollectedTest) {
        let name = test.desc.name.as_str();
        self.cases.started(name);
        let message = json!({
            "schema": CASE_EVENT_SCHEMA,
            "type": "test",
            "event": "started",
            "name": name,
        });
        self.print_message(&message);
    }

    pub(crate) fn test_timed_out(&mut self, test: &CollectedTest) {
        let name = test.desc.name.as_str();
        let message = json!({
            "schema": CASE_EVENT_SCHEMA,
            "type": "test",
            "event": "timeout",
            "name": name,
        });
        self.print_message(&message);
    }

    pub(crate) fn test_finished(&mut self, test: &CollectedTest, completion: &TestCompletion) {
        let event;
        let name = test.desc.name.as_str();
        self.cases.finished(name);
        let mut maybe_message = None;
        let maybe_stdout = completion.stdout.as_deref().map(String::from_utf8_lossy);

        match completion.outcome {
            TestOutcome::Succeeded => {
                self.passed += 1;
                event = "ok";
            }
            TestOutcome::Failed { message } => {
                self.failed += 1;
                maybe_message = message;
                event = "failed";
            }
            TestOutcome::Ignored => {
                self.ignored += 1;
                maybe_message = test.desc.ignore_message.as_deref();
                event = "ignored";
            }
        };

        // This emits optional fields as `null`, instead of omitting them
        // completely as libtest does, but bootstrap can parse the result
        // either way.
        let json = json!({
            "schema": CASE_EVENT_SCHEMA,
            "type": "test",
            "event": event,
            "name": name,
            "message": maybe_message,
            "stdout": maybe_stdout,
        });

        self.print_message(&json);
    }

    pub(crate) fn suite_finished(&mut self) -> bool {
        let exec_time = self.suite_start.map(|start| (self.now() - start).as_secs_f64());
        let protocol_error = self.cases.finish_error();
        if let Some(error) = protocol_error {
            eprintln!("compiletest case event protocol error: {error}");
        }
        let suite_passed = self.failed == 0 && protocol_error.is_none();

        let event = if suite_passed { "ok" } else { "failed" };
        let message = json!({
            "schema": CASE_EVENT_SCHEMA,
            "type": "suite",
            "event": event,
            "selected_count": self.cases.selected,
            "executed_count": self.passed + self.failed,
            "terminal_count": self.passed + self.failed + self.ignored,
            "protocol_valid": protocol_error.is_none(),
            "protocol_error": protocol_error,
            "passed": self.passed,
            "failed": self.failed,
            "ignored": self.ignored,
            // Compiletest doesn't run any benchmarks, but we still need to set this
            // field to 0 so that bootstrap's JSON parser can read our message.
            "measured": 0,
            "filtered_out": self.filtered_out,
            "exec_time": exec_time,
        });

        self.print_message(&message);
        suite_passed
    }
}

// Trust: a count alone cannot distinguish duplicate terminal events from missing cases.
struct CaseLedger {
    selected: usize,
    started: HashSet<String>,
    terminal: HashSet<String>,
    terminal_events: usize,
    error: Option<&'static str>,
}

impl CaseLedger {
    fn new(selected: usize) -> Self {
        Self {
            selected,
            started: HashSet::new(),
            terminal: HashSet::new(),
            terminal_events: 0,
            error: None,
        }
    }

    fn started(&mut self, name: &str) {
        if !self.started.insert(name.to_owned()) {
            self.error.get_or_insert("duplicate selected test identity");
        }
    }

    fn finished(&mut self, name: &str) {
        self.terminal_events += 1;
        if !self.started.contains(name) {
            self.error.get_or_insert("terminal event without start");
        }
        if !self.terminal.insert(name.to_owned()) {
            self.error.get_or_insert("duplicate terminal event");
        }
    }

    fn finish_error(&self) -> Option<&'static str> {
        self.error
            .or_else(|| (self.selected == 0).then_some("no tests selected"))
            .or_else(|| {
                (self.started.len() != self.selected).then_some("missing selected test starts")
            })
            .or_else(|| {
                (self.terminal.len() != self.selected || self.terminal_events != self.selected)
                    .then_some("missing terminal events")
            })
    }
}

#[cfg(test)]
mod tests;
