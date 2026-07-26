// The ObservableTrace schema: the exact serde mirror of the JSON emitted by
// js/trace_driver.mjs. Every field here is a spec-mandated observable or a
// declared projection cap — nothing engine-incidental. Two heads are
// trace-equal iff their parsed `ObservableTrace` values are `==`.
//
// Language-agnostic core: ObservableTrace / HostEvent / Completion /
// ProjectionCaps (a Python front end reuses these unchanged).
// JS-specific observable set: ProjectedValue / PropKey / ThrownProjection
// (property enumeration order, -0 vs +0, NaN, symbol descriptions, accessor
// non-invocation, error constructor identity).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use serde::{Deserialize, Serialize};

/// Schema identity stamped into every trace by every head.
pub const SCHEMA_VERSION: &str = "trust.js.observable-trace.v1";

/// The stdout sentinel prefixing the single trace line a driver run emits.
pub const TRACE_SENTINEL: &str = "__TRUST_JS_TRACE_V1__";

/// The full behavioral projection of one engine run: ordered host effects
/// plus the completion. This is the value every oracle head serializes to and
/// the only thing the differential harness ever compares.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ObservableTrace {
    pub schema: String,
    /// Projection caps are part of the projection's identity; absent only on
    /// the driver-internal-error path.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub caps: Option<ProjectionCaps>,
    pub events: Vec<HostEvent>,
    pub completion: Completion,
}

/// Deterministic caps bounding the deep-print walk and the virtual timer
/// drain. A projection that walked unboundedly would be nondeterministic
/// under resource exhaustion, so the caps are declared observables.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProjectionCaps {
    pub depth: u32,
    pub keys: u32,
    pub nodes: u32,
    pub string: u32,
    pub timers: u32,
}

/// One ordered host effect.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "k", rename_all = "lowercase")]
pub enum HostEvent {
    /// console.log/info/debug/trace and the test262 `print` hook.
    Stdout { v: Vec<ProjectedValue> },
    /// console.warn/error.
    Stderr { v: Vec<ProjectedValue> },
    /// A firewall-recorded host access (e.g. "fetch", "process.exit",
    /// "timer-cap").
    Host { v: String },
}

/// How the run completed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "k", rename_all = "kebab-case")]
pub enum Completion {
    /// Normal completion. `v` is the deep-printed script completion value,
    /// present only when the case manifest opts in (`completion_witness`).
    /// Calibration ruling (2026-07-21): V8 and JSC genuinely diverge on
    /// spec-corner eval completion values (1,153 runs in the pre-calibration
    /// sweep) and no test relies on them, so the witness is opt-in — an
    /// observable for engine-vs-sem differential work, not for Node-vs-Bun
    /// calibration.
    Normal {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        v: Option<ProjectedValue>,
    },
    /// The evaluated code threw. `phase` distinguishes a throw escaping the
    /// virtual-timer drain ("timer") from the main evaluation (absent).
    Throw {
        v: ThrownProjection,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        phase: Option<String>,
    },
    /// A harness include (assert.js, sta.js, ...) failed to evaluate — a
    /// corpus/assembly fault, never a test observable.
    HarnessIncludeError { v: ThrownProjection },
    /// The driver itself failed — a harness error, never a test observable.
    DriverError { v: ThrownProjection },
}

/// The deep-print projection of one JS value. Strings arrive pre-escaped to
/// pure ASCII by the driver (code-unit escapes, so lone surrogates survive
/// the JSON layer); `num` carries the canonical ECMA-262 Number::toString
/// repr with "-0" distinguished from "0".
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "t", rename_all = "lowercase")]
pub enum ProjectedValue {
    Undefined,
    Null,
    Bool {
        v: bool,
    },
    Num {
        v: String,
    },
    Bigint {
        v: String,
    },
    Str {
        v: String,
    },
    Sym {
        /// Well-known symbol name ("Symbol.iterator", ...), if intrinsic.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        wk: Option<String>,
        /// Escaped description; None both for absent description and for a
        /// well-known symbol (which carries `wk` instead).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        v: Option<String>,
    },
    Fun {
        /// Own `name` data descriptor only; an accessor name is never read.
        name: Option<String>,
    },
    Obj {
        /// Pre-order node id, referenced by `Circ` back-edges.
        id: u64,
        /// Nearest intrinsic prototype on the chain, by identity — never by
        /// invoking user code.
        cls: Option<String>,
        /// Own properties in spec enumeration order (integer keys ascending,
        /// then insertion order, then symbols). None iff introspection threw.
        props: Option<Vec<(PropKey, ProjectedValue)>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        unintrospectable: Option<bool>,
        /// Present iff the key walk was truncated; carries the true own-key
        /// count.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        keycap: Option<u64>,
    },
    /// Cycle back-reference to a previously printed node.
    Circ {
        #[serde(rename = "ref")]
        target: u64,
    },
    /// Depth cap reached; the node still gets an id so cycles through it stay
    /// stable.
    Depthcap {
        id: u64,
    },
    /// Total-node cap reached.
    Nodecap,
    /// Introspection threw mid-print (hostile proxy trap).
    Unprintable,
    /// The property vanished between ownKeys and its descriptor read.
    Vanished,
    /// A non-enumerable data property (enumerability is an observable).
    Nonenum {
        v: Box<ProjectedValue>,
    },
    /// An accessor property, recorded WITHOUT being invoked.
    Accessor {
        get: bool,
        set: bool,
    },
}

/// The test262 async-failure marker prefix. The async harness
/// (harness/doneprintHandle.js) reports a failed async test by `print`-ing
/// `Test262:AsyncTestFailure:<name>: <message>` (or the non-object fallback
/// `Test262:AsyncTestFailure:Test262Error: <String(error)>`), captured by the
/// driver's `print` hook as a Stdout event carrying one string arg.
pub const ASYNC_FAILURE_MARKER_PREFIX: &str = "Test262:AsyncTestFailure:";

/// The test262 async-success marker: `harness/doneprintHandle.js` `print`s this
/// exact string when `$DONE` is called with no error.
pub const ASYNC_COMPLETE_MARKER: &str = "Test262:AsyncTestComplete";

/// Is this event the test262 async completion signal — the success marker
/// (`Test262:AsyncTestComplete`) or any failure marker
/// (`Test262:AsyncTestFailure:*`)? Only a Stdout event carrying a single string
/// argument (how the harness `print`s it) qualifies.
fn is_async_completion_marker(event: &HostEvent) -> bool {
    let HostEvent::Stdout { v } = event else {
        return false;
    };
    let [ProjectedValue::Str { v: s }] = v.as_slice() else {
        return false;
    };
    s == ASYNC_COMPLETE_MARKER || s.starts_with(ASYNC_FAILURE_MARKER_PREFIX)
}

/// Normalize test262 async-failure markers to error identity only.
///
/// The `<message>` tail of an `AsyncTestFailure` marker is unspecified,
/// engine-divergent text (dynamic-import absolute paths, V8-vs-JSC error
/// phrasings, ...) — exactly the class the thrown-completion projection
/// already strips to `.name` (see [`ThrownProjection`]). Without this pass the
/// async failure observable leaks that message text, so two heads that agree
/// on the failure identity still diverge on wording. This rewrites any Stdout
/// event carrying a single string arg that starts with
/// [`ASYNC_FAILURE_MARKER_PREFIX`] to keep `Test262:AsyncTestFailure:<name>`
/// and drop `: <message>`, matching the sync-throw projection: error identity,
/// never message text.
///
/// `<name>` is the token between the prefix and the first `": "` (an error
/// `.name` like `"TypeError"`, or the `"Test262Error"` fallback marker). The
/// `Test262:AsyncTestComplete` success marker carries no message and is left
/// untouched. The rewrite is idempotent (an already message-free marker maps
/// to itself) and a no-op on any trace without such a marker (so slices with
/// no async cases, e.g. S0, are unchanged).
pub fn normalize_async_completion_markers(trace: &mut ObservableTrace) {
    for event in &mut trace.events {
        let HostEvent::Stdout { v } = event else {
            continue;
        };
        // The harness `print`s the marker as a single string argument.
        let [ProjectedValue::Str { v: s }] = v.as_mut_slice() else {
            continue;
        };
        let Some(rest) = s.strip_prefix(ASYNC_FAILURE_MARKER_PREFIX) else {
            continue;
        };
        // Drop everything from the first ": " onward — the message tail. The
        // prefix, name, and the ": " separator are all ASCII, so the driver's
        // code-unit escaping never disturbs this scan.
        let name_len = rest.find(": ").unwrap_or(rest.len());
        if name_len == rest.len() {
            continue; // already message-free (e.g. a re-normalized marker)
        }
        s.truncate(ASYNC_FAILURE_MARKER_PREFIX.len() + name_len);
    }

    // The test262 async protocol adjudicates a test at its FIRST completion
    // signal: a conformance runner reads the harness output until the first
    // `Test262:AsyncTestComplete` / `Test262:AsyncTestFailure:*` line and stops.
    // Everything printed after it is post-completion noise. In particular a
    // test whose promise chain fires `$DONE` more than once — e.g.
    // `f().then($DONE, h).then($DONE, $DONE)` — prints the success marker a
    // fulfillment-path-dependent number of times (Node twice when `f` fulfills,
    // Bun once when it rejects then recovers in `h`) even though BOTH engines
    // PASS. The marker COUNT and any post-first-marker tail are not observables,
    // so truncate the event stream at (and including) the first completion
    // marker to match the protocol's verdict. This can never hide a real
    // pass/fail split: that difference is at the FIRST marker, which survives.
    if let Some(idx) = trace.events.iter().position(is_async_completion_marker) {
        trace.events.truncate(idx + 1);
    }
}

/// A property key: an escaped string key, or a symbol key.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum PropKey {
    Str(String),
    Sym { sym: Box<ProjectedValue> },
}

/// A thrown value, projected to constructor identity + `.name` only — never
/// message text (messages are unspecified and engine-divergent).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "t", rename_all = "lowercase")]
pub enum ThrownProjection {
    /// A thrown primitive (throw 42, throw "x").
    Prim { v: ProjectedValue },
    /// A thrown object/function.
    Error {
        /// Nearest intrinsic prototype ("Error:TypeError", "Object", ...).
        ctor: Option<String>,
        /// `.name` resolved through the prototype chain, data descriptors
        /// only.
        name: Option<String>,
        /// proto.constructor.name (data descriptors only) — distinguishes
        /// Test262Error and user error classes.
        ctor_name: Option<String>,
    },
}
