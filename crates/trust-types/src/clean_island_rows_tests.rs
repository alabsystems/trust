// Unit tests for the island-row transport: it parses through the one transport
// parser, and `validate` refuses every message no honest producer writes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;
use crate::{TransportMessage, parse_transport_payload};

const ID: &str = "0123456789abcdef";

fn payload(phase: &str, complete: bool, rows: &str) -> String {
    let problems = if complete { "[]" } else { r#"["island 2's text could not be recovered"]"# };
    format!(
        r#"{{"type":"clean_island_rows","schema":"trust.clean-island-rows.v1","crate_name":"demo","package_name":"demo","verification_session":"s","primary_package":true,"phase":"{phase}","islands":2,"complete":{complete},"problems":{problems},"rows":[{rows}]}}"#
    )
}

fn row(key: &str, status: &str, stop: &str, basis: Option<&str>) -> String {
    let basis = basis.map(|basis| format!(r#","basis":"{basis}""#)).unwrap_or_default();
    format!(
        r#"{{"key":"{key}","kind":"lean:theorem","status":"{status}","stop":"{stop}"{basis},"file":"src/lib.rs","line":4,"col":5,"source":null}}"#
    )
}

fn parsed(text: &str) -> CleanIslandRowsTransport {
    match parse_transport_payload(text).expect("an island-rows payload parses") {
        TransportMessage::CleanIslandRows(rows) => rows,
        other => panic!("parsed as {other:?}"),
    }
}

#[test]
fn a_clean_island_rows_payload_parses_and_is_validated() {
    let proved = row(&format!("demo::Demo.t#{ID}"), "proved", "solved", None);
    let refused = row(
        &format!("demo::Demo.u#{ID}"),
        "failed",
        "solver-incomplete",
        Some("unproved_fail_closed"),
    );
    let message = parsed(&payload("verified", true, &format!("{proved},{refused}")));
    assert_eq!(message.validate(), Ok(()));
    assert_eq!(message.phase, CleanIslandPhase::Verified);
    assert_eq!(message.rows[0].verdict(), Some(CleanIslandRowVerdict::Proved));
    assert_eq!(message.rows[1].verdict(), Some(CleanIslandRowVerdict::ProofRefused));
    // The wire form round-trips through the one parser.
    let wire = serde_json::to_string(&TransportMessage::CleanIslandRows(message.clone())).unwrap();
    assert_eq!(parsed(&wire), message);

    // A proved row only in a verified, complete payload.
    let refuse = |text: String, why: &str| {
        let error = parsed(&text).validate().expect_err(why);
        assert!(error.contains(why), "{error}");
    };
    refuse(
        payload("front-end-error", true, &proved),
        "is proved in a payload that is front-end-error",
    );
    refuse(
        payload("verified", false, &proved),
        "is proved in a payload that is verified and incomplete",
    );
    // The same rows unproved are fine on either path.
    let unknown = row(&format!("demo::Demo.t#{ID}"), "unknown", "not-dispatched", None);
    assert_eq!(parsed(&payload("front-end-error", false, &unknown)).validate(), Ok(()));
    // A key without the crate prefix, or with a malformed local id.
    refuse(
        payload("verified", true, &row(&format!("other::Demo.t#{ID}"), "proved", "solved", None)),
        "does not name a declaration of crate `demo`",
    );
    refuse(
        payload("verified", true, &row(&format!("Demo.t#{ID}"), "proved", "solved", None)),
        "does not name a declaration of crate `demo`",
    );
    refuse(
        payload("verified", true, &row("demo::Demo.t#0123", "proved", "solved", None)),
        "is not `<name>#<16 hex>`",
    );
    // Only the four island verdicts.
    for (status, stop, basis) in [
        ("failed", "solved", Some("refuted")),
        ("failed", "solver-incomplete", None),
        ("proved", "not-dispatched", None),
        ("unknown", "timeout", None),
        ("runtime_checked", "solved", None),
        ("unknown", "unsupported", Some("unproved_fail_closed")),
    ] {
        refuse(
            payload("verified", true, &row(&format!("demo::Demo.t#{ID}"), status, stop, basis)),
            "which no island row can",
        );
    }
    // `complete` agrees with `problems`; keys in order, each once.
    let mut text = payload("verified", true, &unknown);
    text = text.replace(r#""problems":[]"#, r#""problems":["x"]"#);
    refuse(text, "complete=true with 1 problem(s)");
    refuse(payload("verified", true, &format!("{unknown},{unknown}")), "out of key order");
    refuse(payload("verified", true, &format!("{refused},{proved}")), "out of key order");
}

#[test]
fn a_worse_verdict_wins_a_merge() {
    use CleanIslandRowVerdict::*;
    assert_eq!(Proved.worse(NotDispatched), NotDispatched);
    assert_eq!(NotDispatched.worse(ProofRefused), ProofRefused);
    assert_eq!(Unsupported.worse(NotDispatched), NotDispatched);
    assert_eq!(Proved.worse(Unsupported), Unsupported);
    assert_eq!(Proved.worse(Proved), Proved);
}

#[test]
fn a_unit_with_no_island_states_it_and_has_no_row() {
    // A unit the compiler reached with no island publishes `islands: 0`, so a
    // unit that published nothing is never read as one with no island.
    let none = payload("verified", true, "").replace(r#""islands":2"#, r#""islands":0"#);
    assert_eq!(parsed(&none).validate(), Ok(()));
    let unknown = row(&format!("demo::Demo.t#{ID}"), "unknown", "not-dispatched", None);
    let error =
        parsed(&payload("verified", true, &unknown).replace(r#""islands":2"#, r#""islands":0"#))
            .validate()
            .expect_err("a row of a unit with no island");
    assert!(error.contains("island rows of a unit with no island"), "{error}");
}
