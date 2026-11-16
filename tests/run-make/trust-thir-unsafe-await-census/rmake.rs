use std::collections::BTreeSet;
use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rustc_path};

// `=info`, not `=debug`, and that is load-bearing rather than cosmetic. A stage
// built with the default `rust.debug-logging = false` compiles tracing's DEBUG
// callsites out entirely (bootstrap pushes `max_level_info`), so a `debug!`
// census cannot carry a run-make contract at all: the events do not exist, and
// `tracing-subscriber` prints `some trace filter directives would enable traces
// that are disabled statically` instead. The census messages this recipe reads
// are `info!` for that reason, matching `trust_ir_flip`.
const LOG_TARGET: &str = "rustc_mir_build::trust_unsafe_source_events=info";
const EVENT: &str = "Trust THIR unsafe source event (diagnostic only)";
const COMPLETE: &str = "Trust THIR requires_unsafe body scan complete (diagnostic only)";
const EXPECTED_DEREF_SPANS: [&str; 2] =
    ["await-census.rs:4:39: 4:43", "await-census.rs:5:22: 5:26"];

fn field<'a>(line: &'a str, name: &str) -> &'a str {
    let prefix = format!("{name}=");
    line.split_whitespace()
        .find_map(|word| word.strip_prefix(&prefix))
        .map(|value| value.trim_end_matches(','))
        .unwrap_or_else(|| panic!("missing {name} in THIR event record: {line}"))
}

fn owner_index(line: &str) -> u32 {
    field(line, "body_owner_index").parse().expect("numeric local body owner index")
}

fn source_span(line: &str) -> &str {
    let span = line
        .split_once(", span=")
        .and_then(|(_, rest)| rest.split_once(", span_lo="))
        .map(|(span, _)| span)
        .unwrap_or_else(|| panic!("missing source span in THIR event record: {line}"));
    span.split_once(" (#")
        .map(|(location, _)| location)
        .unwrap_or_else(|| panic!("missing span context in THIR event record: {line}"))
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }

    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };
    let output = cmd(&trustc)
        .env("RUSTC_LOG", LOG_TARGET)
        .args([
            "--crate-name=await_census",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=mir",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=off",
            "await-census.rs",
            "-o",
            "await-census.mir",
        ])
        .run();
    let stderr = output.stderr_utf8();
    let events: Vec<_> = stderr.lines().filter(|line| line.contains(EVENT)).collect();
    let completes: Vec<_> = stderr.lines().filter(|line| line.contains(COMPLETE)).collect();

    // A LIVENESS GUARD, and it is strictly additional — it can only turn one
    // failure into a more legible failure, never admit a missing event. Without
    // it, a trustc that statically dropped the census level fails every
    // assertion below as "no events", which reads as a census defect and is not
    // one. Measured 2026-09-27: that is exactly how this test failed.
    assert!(
        !completes.is_empty(),
        "the THIR unsafe source census produced no rows at all, so the assertions below \
         would be about an observation channel that is not reaching stderr rather than \
         about the census. A `some trace filter directives would enable traces that are \
         disabled statically` line in the output below means this trustc compiled the \
         census level out (`rust.debug-logging = false` + a `debug!` callsite):\n{stderr}"
    );

    // The two user-written dereferences are in distinct coroutine THIR bodies:
    // the awaited async block and the enclosing async function body.
    let derefs: Vec<_> = events
        .iter()
        .copied()
        .filter(|line| {
            field(line, "kind") == "DerefOfRawPointer"
                && field(line, "safety_scope") == "ExplicitUnsafeBlock"
                && field(line, "owner_def_kind") == "Closure"
        })
        .collect();
    assert_eq!(derefs.len(), 2, "expected both coroutine source events: {stderr}");
    let spans: BTreeSet<_> = derefs.iter().map(|line| source_span(line)).collect();
    assert_eq!(spans.len(), derefs.len(), "duplicate dereference source span: {stderr}");
    assert_eq!(
        spans,
        EXPECTED_DEREF_SPANS.into_iter().collect(),
        "missing or unexpected dereference source span: {stderr}"
    );
    let owners: BTreeSet<_> = derefs.iter().map(|line| owner_index(line)).collect();
    assert_eq!(owners.len(), 2, "async bodies must retain distinct owners: {stderr}");

    for owner in owners {
        let body_events: Vec<_> =
            events.iter().copied().filter(|line| owner_index(line) == owner).collect();
        let body_completes: Vec<_> =
            completes.iter().copied().filter(|line| owner_index(line) == owner).collect();
        assert_eq!(body_completes.len(), 1, "expected one completed scan: {stderr}");
        let count: usize =
            field(body_completes[0], "event_count").parse().expect("numeric per-body event count");
        assert_eq!(count, body_events.len(), "event rows must reconcile: {stderr}");
        let ordinals: BTreeSet<usize> = body_events
            .iter()
            .map(|line| field(line, "occurrence").parse().expect("numeric occurrence"))
            .collect();
        assert_eq!(ordinals, (0..count).collect(), "event ordinals must be complete: {stderr}");
        assert!(
            body_events.iter().any(|line| field(line, "origin") == "NonBuiltin"),
            "source dereference must not be classified as compiler builtin: {stderr}"
        );
    }
}
