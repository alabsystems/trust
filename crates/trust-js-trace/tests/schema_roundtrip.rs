// Schema-contract tests: the Rust types must parse exactly the JSON the
// driver emits, and re-serialize to an equal value. Sample lines here are
// pinned copies of real driver output shapes — if the driver's emission
// format changes, these must change WITH it (they are the two sides of one
// contract).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use trust_js_trace::{
    extract_trace, explain_divergence, normalize_async_completion_markers, traces_equal,
    Completion, HostEvent, ObservableTrace, ProjectedValue, PropKey, ThrownProjection,
    ASYNC_FAILURE_MARKER_PREFIX, SCHEMA_VERSION, TRACE_SENTINEL,
};

const NORMAL_TRACE: &str = r#"{"schema":"trust.js.observable-trace.v1","caps":{"depth":8,"keys":64,"nodes":4096,"string":4096,"timers":10000},"events":[{"k":"stdout","v":[{"t":"str","v":"hello"},{"t":"num","v":"-0"}]},{"k":"host","v":"timer-cap"}],"completion":{"k":"normal","v":{"t":"undefined"}}}"#;

const THROW_TRACE: &str = r#"{"schema":"trust.js.observable-trace.v1","caps":{"depth":8,"keys":64,"nodes":4096,"string":4096,"timers":10000},"events":[],"completion":{"k":"throw","v":{"t":"error","ctor":"Error:TypeError","name":"TypeError","ctor_name":"TypeError"}}}"#;

const OBJECT_WITNESS_TRACE: &str = r#"{"schema":"trust.js.observable-trace.v1","caps":{"depth":8,"keys":64,"nodes":4096,"string":4096,"timers":10000},"events":[],"completion":{"k":"normal","v":{"t":"obj","id":0,"cls":"Object","props":[["a",{"t":"num","v":"NaN"}],["b",{"t":"accessor","get":true,"set":false}],[{"sym":{"t":"sym","wk":"Symbol.iterator"}},{"t":"nonenum","v":{"t":"circ","ref":0}}]]}}}"#;

#[test]
fn normal_trace_roundtrips() {
    let t: ObservableTrace = serde_json::from_str(NORMAL_TRACE).unwrap();
    assert_eq!(t.events.len(), 2);
    match &t.events[0] {
        HostEvent::Stdout { v } => {
            assert_eq!(v[0], ProjectedValue::Str { v: "hello".into() });
            assert_eq!(v[1], ProjectedValue::Num { v: "-0".into() });
        }
        other => panic!("wrong event: {other:?}"),
    }
    let json = serde_json::to_string(&t).unwrap();
    let t2: ObservableTrace = serde_json::from_str(&json).unwrap();
    assert!(traces_equal(&t, &t2));
}

#[test]
fn throw_trace_projects_ctor_identity_only() {
    let t: ObservableTrace = serde_json::from_str(THROW_TRACE).unwrap();
    match &t.completion {
        Completion::Throw { v, phase } => {
            assert!(phase.is_none());
            assert_eq!(
                *v,
                ThrownProjection::Error {
                    ctor: Some("Error:TypeError".into()),
                    name: Some("TypeError".into()),
                    ctor_name: Some("TypeError".into()),
                }
            );
        }
        other => panic!("wrong completion: {other:?}"),
    }
}

#[test]
fn object_witness_preserves_order_symbols_and_cycles() {
    let t: ObservableTrace = serde_json::from_str(OBJECT_WITNESS_TRACE).unwrap();
    let Completion::Normal { v: Some(ProjectedValue::Obj { props, .. }) } = &t.completion else {
        panic!("wrong completion: {:?}", t.completion);
    };
    let props = props.as_ref().unwrap();
    assert_eq!(props.len(), 3);
    assert_eq!(props[0].0, PropKey::Str("a".into()));
    // NaN survives as canonical text.
    assert_eq!(props[0].1, ProjectedValue::Num { v: "NaN".into() });
    // Accessors are recorded, never invoked.
    assert_eq!(
        props[1].1,
        ProjectedValue::Accessor {
            get: true,
            set: false
        }
    );
    // Symbol key + non-enumerable data prop + cycle back-reference.
    match (&props[2].0, &props[2].1) {
        (PropKey::Sym { sym }, ProjectedValue::Nonenum { v }) => {
            assert_eq!(
                **sym,
                ProjectedValue::Sym {
                    wk: Some("Symbol.iterator".into()),
                    v: None
                }
            );
            assert_eq!(**v, ProjectedValue::Circ { target: 0 });
        }
        other => panic!("wrong symbol prop: {other:?}"),
    }
    // Round-trip stability.
    let json = serde_json::to_string(&t).unwrap();
    assert_eq!(t, serde_json::from_str::<ObservableTrace>(&json).unwrap());
}

#[test]
fn sentinel_extraction_takes_last_line_and_validates_schema() {
    let stdout = format!(
        "engine noise\nmore noise\n{TRACE_SENTINEL}{NORMAL_TRACE}\n"
    );
    let t = extract_trace(stdout.as_bytes()).unwrap();
    assert_eq!(t.schema, trust_js_trace::SCHEMA_VERSION);

    let err = extract_trace(b"no sentinel here").unwrap_err();
    assert!(err.to_string().contains("no trace sentinel"), "{err}");

    let bad = format!("{TRACE_SENTINEL}{{\"schema\":\"wrong.v9\",\"events\":[],\"completion\":{{\"k\":\"normal\",\"v\":{{\"t\":\"undefined\"}}}}}}");
    let err = extract_trace(bad.as_bytes()).unwrap_err();
    assert!(err.to_string().contains("schema mismatch"), "{err}");
}

#[test]
fn divergence_explanation_localizes_first_difference() {
    let a: ObservableTrace = serde_json::from_str(NORMAL_TRACE).unwrap();
    let b: ObservableTrace = serde_json::from_str(THROW_TRACE).unwrap();
    assert!(explain_divergence(&a, &a).is_none());
    let why = explain_divergence(&a, &b).unwrap();
    // First difference is the event stream, not the completion.
    assert!(why.starts_with("event"), "{why}");
}

#[test]
fn normal_completion_witness_is_optional() {
    // Calibration default: no witness.
    let bare = r#"{"schema":"trust.js.observable-trace.v1","caps":{"depth":8,"keys":64,"nodes":4096,"string":4096,"timers":10000},"events":[],"completion":{"k":"normal"}}"#;
    let t: ObservableTrace = serde_json::from_str(bare).unwrap();
    assert_eq!(t.completion, Completion::Normal { v: None });
    let json = serde_json::to_string(&t).unwrap();
    assert!(!json.contains("\"v\""), "None witness must not serialize: {json}");
    // The driver only projects the completion value behind the manifest flag.
    assert!(
        trust_js_trace::TRACE_DRIVER_SOURCE.contains("manifest.completion_witness === true"),
        "driver lost the completion-witness gate"
    );
}

// --- async-failure-marker normalization (projection_too_strong fix) ---

fn stdout_str(s: &str) -> HostEvent {
    HostEvent::Stdout {
        v: vec![ProjectedValue::Str { v: s.to_string() }],
    }
}

fn trace_with_events(events: Vec<HostEvent>) -> ObservableTrace {
    ObservableTrace {
        schema: SCHEMA_VERSION.to_string(),
        caps: None,
        events,
        completion: Completion::Normal { v: None },
    }
}

fn normalized_marker(msg_arg: &str) -> String {
    let mut t = trace_with_events(vec![stdout_str(msg_arg)]);
    normalize_async_completion_markers(&mut t);
    match &t.events[0] {
        HostEvent::Stdout { v } => match &v[0] {
            ProjectedValue::Str { v } => v.clone(),
            other => panic!("wrong arg: {other:?}"),
        },
        other => panic!("wrong event: {other:?}"),
    }
}

#[test]
fn async_failure_marker_drops_message_keeping_name() {
    // The object form: name is the token before the first ": ".
    assert_eq!(
        normalized_marker("Test262:AsyncTestFailure:TypeError: Cannot read x of undefined"),
        "Test262:AsyncTestFailure:TypeError"
    );
    // The non-object fallback form normalizes to the fallback marker.
    assert_eq!(
        normalized_marker(
            "Test262:AsyncTestFailure:Test262Error: Expected a Foo but got a Bar at /abs/path"
        ),
        "Test262:AsyncTestFailure:Test262Error"
    );
    // A message that itself contains ": " is still cut at the FIRST separator.
    assert_eq!(
        normalized_marker("Test262:AsyncTestFailure:RangeError: bad: value: here"),
        "Test262:AsyncTestFailure:RangeError"
    );
    // Empty message tail (`: ` then nothing) still strips to the name.
    assert_eq!(
        normalized_marker("Test262:AsyncTestFailure:SyntaxError: "),
        "Test262:AsyncTestFailure:SyntaxError"
    );
}

#[test]
fn async_failure_normalization_is_idempotent_and_leaves_others_untouched() {
    // Already message-free: unchanged (idempotent).
    assert_eq!(
        normalized_marker("Test262:AsyncTestFailure:TypeError"),
        "Test262:AsyncTestFailure:TypeError"
    );
    // The success marker is never a failure marker: untouched.
    assert_eq!(
        normalized_marker("Test262:AsyncTestComplete"),
        "Test262:AsyncTestComplete"
    );
    // Ordinary user stdout is untouched.
    assert_eq!(normalized_marker("hello: world"), "hello: world");
    // Prefix constant matches the harness contract.
    assert_eq!(ASYNC_FAILURE_MARKER_PREFIX, "Test262:AsyncTestFailure:");
}

#[test]
fn async_failure_normalization_makes_message_only_divergence_equal() {
    // Two heads that agree on the failure identity but differ only in the
    // message tail become trace-equal after normalization.
    let mut a = trace_with_events(vec![stdout_str(
        "Test262:AsyncTestFailure:TypeError: message from engine A",
    )]);
    let mut b = trace_with_events(vec![stdout_str(
        "Test262:AsyncTestFailure:TypeError: totally different wording from engine B",
    )]);
    assert!(!traces_equal(&a, &b), "pre-normalization they must differ");
    normalize_async_completion_markers(&mut a);
    normalize_async_completion_markers(&mut b);
    assert!(traces_equal(&a, &b), "post-normalization they must match");

    // But a genuine identity divergence (different .name) still diverges.
    let mut c = trace_with_events(vec![stdout_str(
        "Test262:AsyncTestFailure:RangeError: x",
    )]);
    normalize_async_completion_markers(&mut c);
    assert!(!traces_equal(&a, &c), "different error identity must still diverge");
}

#[test]
fn async_failure_normalization_only_touches_single_string_stdout() {
    // A multi-arg stdout whose first arg looks like a marker is NOT a harness
    // marker (the harness prints exactly one string) and is left untouched.
    let mut multi = trace_with_events(vec![HostEvent::Stdout {
        v: vec![
            ProjectedValue::Str {
                v: "Test262:AsyncTestFailure:TypeError: msg".to_string(),
            },
            ProjectedValue::Num { v: "1".to_string() },
        ],
    }]);
    let before = multi.clone();
    normalize_async_completion_markers(&mut multi);
    assert_eq!(multi, before, "multi-arg stdout must be untouched");

    // A stderr event is never the async print channel.
    let mut err = trace_with_events(vec![HostEvent::Stderr {
        v: vec![ProjectedValue::Str {
            v: "Test262:AsyncTestFailure:TypeError: msg".to_string(),
        }],
    }]);
    let before = err.clone();
    normalize_async_completion_markers(&mut err);
    assert_eq!(err, before, "stderr must be untouched");
}

#[test]
fn async_completion_truncates_at_first_marker_double_done() {
    // The observed double-$DONE artifact: a tolerant test
    // `f().then($DONE, h).then($DONE, $DONE)` prints AsyncTestComplete twice on
    // an engine where `f` fulfills (Node) but once where it rejects-then-recovers
    // (Bun). Both PASS. After normalization both truncate to a single completion.
    let mut node = trace_with_events(vec![
        stdout_str("Test262:AsyncTestComplete"),
        stdout_str("Test262:AsyncTestComplete"),
    ]);
    let mut bun = trace_with_events(vec![stdout_str("Test262:AsyncTestComplete")]);
    assert!(!traces_equal(&node, &bun), "pre-normalization: 2 vs 1 markers differ");
    normalize_async_completion_markers(&mut node);
    normalize_async_completion_markers(&mut bun);
    assert_eq!(node.events.len(), 1, "truncated to the first completion marker");
    assert!(traces_equal(&node, &bun), "post-normalization: both single completion");
}

#[test]
fn async_completion_truncation_preserves_precompletion_and_pass_fail_split() {
    // Output BEFORE the first completion marker is kept; only the tail is cut.
    let mut t = trace_with_events(vec![
        stdout_str("log line"),
        stdout_str("Test262:AsyncTestComplete"),
        stdout_str("post-completion noise"),
        stdout_str("Test262:AsyncTestComplete"),
    ]);
    normalize_async_completion_markers(&mut t);
    assert_eq!(t.events.len(), 2, "keep the pre-completion event + first marker");
    assert_eq!(t.events[0], stdout_str("log line"));
    assert_eq!(t.events[1], stdout_str("Test262:AsyncTestComplete"));

    // A genuine pass/fail split is at the FIRST marker, so it survives truncation.
    let mut pass = trace_with_events(vec![stdout_str("Test262:AsyncTestComplete")]);
    let mut fail = trace_with_events(vec![stdout_str(
        "Test262:AsyncTestFailure:Test262Error: assertion x",
    )]);
    normalize_async_completion_markers(&mut pass);
    normalize_async_completion_markers(&mut fail);
    assert!(!traces_equal(&pass, &fail), "pass vs fail must still diverge");

    // A failure BEFORE a later stray complete is the adjudicated verdict.
    let mut fail_then_complete = trace_with_events(vec![
        stdout_str("Test262:AsyncTestFailure:TypeError: boom"),
        stdout_str("Test262:AsyncTestComplete"),
    ]);
    normalize_async_completion_markers(&mut fail_then_complete);
    assert_eq!(fail_then_complete.events.len(), 1);
    assert_eq!(
        fail_then_complete.events[0],
        stdout_str("Test262:AsyncTestFailure:TypeError")
    );
}

#[test]
fn driver_bytes_are_pinned_into_evidence_identity() {
    let h = trust_js_trace::trace_driver_sha256();
    assert_eq!(h.len(), 64);
    assert!(trust_js_trace::TRACE_DRIVER_SOURCE.contains(TRACE_SENTINEL));
    // The driver's declared caps must match the schema sample caps above —
    // one projection identity on both sides of the contract.
    for needle in [
        "const MAX_DEPTH = 8",
        "const MAX_KEYS = 64",
        "const MAX_NODES = 4096",
        "const MAX_STRING = 4096",
        "const TIMER_CAP = 10000",
    ] {
        assert!(
            trust_js_trace::TRACE_DRIVER_SOURCE.contains(needle),
            "driver caps drifted from schema contract: {needle}"
        );
    }
}
