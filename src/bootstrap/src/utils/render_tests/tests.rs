use std::fs;

use super::{CASE_EVENT_SCHEMA, CaseEventForwarder, Message, validate_raw_stream_mode};
use crate::utils::exec::BootstrapCommand;

fn forward_line(events: &mut CaseEventForwarder<Vec<u8>>, line: &str) {
    let value: serde_json::Value = serde_json::from_str(line).unwrap();
    let is_case_event =
        value.get("schema").and_then(serde_json::Value::as_str) == Some(CASE_EVENT_SCHEMA);
    let message: Message = serde_json::from_value(value).unwrap();
    events.forward_parsed(line.as_bytes(), is_case_event, &message);
}

fn record(events: &mut CaseEventForwarder<Vec<u8>>, value: serde_json::Value) {
    let line = format!("{value}\n");
    forward_line(events, &line);
}

fn start(events: &mut CaseEventForwarder<Vec<u8>>, selected: usize) {
    record(
        events,
        serde_json::json!({
            "schema": CASE_EVENT_SCHEMA,
            "type": "suite",
            "event": "started",
            "test_count": selected,
            "selected_count": selected,
        }),
    );
}

fn test_event(events: &mut CaseEventForwarder<Vec<u8>>, event: &str, name: &str) {
    record(
        events,
        serde_json::json!({
            "schema": CASE_EVENT_SCHEMA,
            "type": "test",
            "event": event,
            "name": name,
        }),
    );
}

fn end(
    events: &mut CaseEventForwarder<Vec<u8>>,
    event: &str,
    selected: usize,
    passed: usize,
    failed: usize,
    ignored: usize,
) {
    record(
        events,
        serde_json::json!({
            "schema": CASE_EVENT_SCHEMA,
            "type": "suite",
            "event": event,
            "selected_count": selected,
            "executed_count": passed + failed,
            "terminal_count": passed + failed + ignored,
            "protocol_valid": true,
            "passed": passed,
            "failed": failed,
            "ignored": ignored,
            "measured": 0,
            "filtered_out": 0,
            "exec_time": 0.0,
        }),
    );
}

#[test]
fn forwards_original_case_json_and_preserves_exact_identity() {
    let mut events = CaseEventForwarder::new(Vec::new());
    start(&mut events, 1);
    let started = format!(
        "{{\"schema\":\"{CASE_EVENT_SCHEMA}\",\"type\":\"test\",\"event\":\"started\",\"name\":\"tests/ui/\\u0061.rs\"}}\n"
    );
    forward_line(&mut events, &started);
    test_event(&mut events, "ok", "tests/ui/a.rs");
    end(&mut events, "ok", 1, 1, 0, 0);
    assert!(String::from_utf8(events.writer.clone()).unwrap().contains(&started));
    assert!(events.finish().is_ok());
}

#[test]
fn creates_distinct_sidecars_with_invocation_arguments() {
    let dir = tempfile::tempdir().unwrap();
    let args = vec!["--suite".to_owned(), "ui".to_owned(), "--mode".to_owned(), "ui".to_owned()];
    drop(CaseEventForwarder::create(dir.path(), args.clone()).unwrap());
    drop(CaseEventForwarder::create(dir.path(), args.clone()).unwrap());

    let paths = fs::read_dir(dir.path()).unwrap().collect::<Result<Vec<_>, _>>().unwrap();
    assert_eq!(paths.len(), 2);
    for entry in paths {
        let contents = fs::read_to_string(entry.path()).unwrap();
        let header: serde_json::Value = serde_json::from_str(&contents).unwrap();
        assert_eq!(header["schema"], CASE_EVENT_SCHEMA);
        assert_eq!(header["type"], "invocation");
        assert_eq!(header["argv"], serde_json::json!(args));
    }
}

#[test]
fn accepts_ignored_case_without_counting_it_as_executed() {
    let mut events = CaseEventForwarder::new(Vec::new());
    start(&mut events, 2);
    test_event(&mut events, "started", "a");
    test_event(&mut events, "started", "b");
    test_event(&mut events, "ok", "a");
    test_event(&mut events, "ignored", "b");
    end(&mut events, "ok", 2, 1, 0, 1);
    assert!(events.finish().is_ok());
}

#[test]
fn accepts_complete_failing_suite() {
    let mut events = CaseEventForwarder::new(Vec::new());
    start(&mut events, 1);
    test_event(&mut events, "started", "a");
    test_event(&mut events, "failed", "a");
    end(&mut events, "failed", 1, 0, 1, 0);
    assert!(events.finish().is_ok());
}

#[test]
fn rejects_untagged_parsed_events_before_suite_start() {
    for line in [
        r#"{"type":"suite","event":"started","test_count":1}"#,
        r#"{"type":"test","event":"started","name":"a"}"#,
    ] {
        let mut events = CaseEventForwarder::new(Vec::new());
        forward_line(&mut events, &format!("{line}\n"));
        start(&mut events, 1);
        test_event(&mut events, "started", "a");
        test_event(&mut events, "ok", "a");
        end(&mut events, "ok", 1, 1, 0, 0);
        assert_eq!(events.finish().unwrap_err(), "untagged or unknown compiletest event");
    }
}

#[test]
fn raw_stream_mode_refuses_compiletest_suite() {
    let mut compiletest = BootstrapCommand::new("compiletest");
    compiletest.args(["--suite", "ui"]);
    assert!(validate_raw_stream_mode(&compiletest).is_err());
    compiletest.mark_as_executed();

    let mut rustdoc_gui = BootstrapCommand::new("rustdoc-gui");
    assert!(validate_raw_stream_mode(&rustdoc_gui).is_ok());
    rustdoc_gui.mark_as_executed();
}

#[test]
fn rejects_duplicate_terminal_even_when_summary_counts_match() {
    let mut events = CaseEventForwarder::new(Vec::new());
    start(&mut events, 2);
    test_event(&mut events, "started", "a");
    test_event(&mut events, "started", "b");
    test_event(&mut events, "ok", "a");
    test_event(&mut events, "ok", "a");
    end(&mut events, "ok", 2, 2, 0, 0);
    assert_eq!(events.finish().unwrap_err(), "duplicate terminal event");
}

#[test]
fn rejects_missing_terminal_despite_success_summary() {
    let mut events = CaseEventForwarder::new(Vec::new());
    start(&mut events, 2);
    test_event(&mut events, "started", "a");
    test_event(&mut events, "started", "b");
    test_event(&mut events, "ok", "a");
    end(&mut events, "ok", 2, 1, 0, 0);
    assert_eq!(events.finish().unwrap_err(), "inconsistent or incomplete compiletest suite");
}

#[test]
fn rejects_zero_case_success_summary() {
    let mut events = CaseEventForwarder::new(Vec::new());
    start(&mut events, 0);
    end(&mut events, "ok", 0, 0, 0, 0);
    assert_eq!(events.finish().unwrap_err(), "empty or inconsistent compiletest selection");
}

#[test]
fn native_success_requires_every_selected_case_to_execute_and_pass() {
    for (event, passed, failed, ignored) in
        [("ok", 1, 0, 0), ("ignored", 0, 0, 1), ("failed", 0, 1, 0)]
    {
        let mut events = CaseEventForwarder::new(Vec::new());
        start(&mut events, 1);
        test_event(&mut events, "started", "selected.rs");
        test_event(&mut events, event, "selected.rs");
        end(&mut events, if failed == 0 { "ok" } else { "failed" }, 1, passed, failed, ignored);
        assert_eq!(events.finish_executed().is_ok(), event == "ok");
    }
    let mut incomplete = CaseEventForwarder::new(Vec::new());
    start(&mut incomplete, 1);
    test_event(&mut incomplete, "started", "selected.rs");
    test_event(&mut incomplete, "ok", "selected.rs");
    assert!(incomplete.finish_executed().is_err());
}
// Trust: the actual production combination runs the postcheck before its
// caller can apply fail-fast, including when the completed child failed.
#[test]
fn retained_fixture_postcheck_runs_after_failed_tests() {
    let events = std::cell::RefCell::new(Vec::new());
    let (passed, input_error) = super::completed_test_and_postcheck(
        || {
            events.borrow_mut().push("failed-child");
            false
        },
        || {
            events.borrow_mut().push("postcheck");
            Ok(())
        },
    );
    assert!(!passed);
    assert!(input_error.is_none());
    assert_eq!(*events.borrow(), ["failed-child", "postcheck"]);
}

#[test]
fn retained_fixture_postcheck_failure_cannot_publish_success() {
    let (passed, input_error) = super::completed_test_and_postcheck(
        || true,
        || Err("retained runtime changed".to_string()),
    );
    assert!(!passed);
    assert_eq!(input_error.as_deref(), Some("retained runtime changed"));
}
