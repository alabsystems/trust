use super::{CaseLedger, Listener};

#[test]
fn zero_case_selection_fails_even_without_test_failures() {
    let mut listener = Listener::new();
    listener.suite_started(0, 1);
    assert!(!listener.suite_finished());
}

#[test]
fn duplicate_terminal_event_fails_even_when_counts_match() {
    let mut cases = CaseLedger::new(2);
    cases.started("tests/ui/a.rs");
    cases.started("tests/ui/b.rs");
    cases.finished("tests/ui/a.rs");
    cases.finished("tests/ui/a.rs");
    assert_eq!(cases.finish_error(), Some("duplicate terminal event"));
}

#[test]
fn missing_terminal_event_fails() {
    let mut cases = CaseLedger::new(2);
    cases.started("tests/ui/a.rs");
    cases.started("tests/ui/b.rs");
    cases.finished("tests/ui/a.rs");
    assert_eq!(cases.finish_error(), Some("missing terminal events"));
}
