// Regression pins for the 38 four-head sem-divergent runs the recorded
// calibration-s1e gate2 found (build/js262/calibration-s1e-gate2/
// sem_divergences.jsonl). All were WRONG traces produced by the new Symbol
// (20.4) / Date (21.4) work; every one is now fixed EXACT (a Node-equal trace),
// grouped into four clusters:
//
//   1. Symbol-keyed properties threaded through Object operations: freeze/seal
//      lock symbol-keyed own properties (SetIntegrityLevel over
//      [[OwnPropertyKeys]]); getOwnPropertyDescriptors includes symbol keys;
//      getOwnPropertySymbols(primitive) goes through ToObject (empty list, not
//      TypeError); object REST destructuring (CopyDataProperties) copies
//      enumerable symbol-keyed own properties in [[OwnPropertyKeys]] order.
//   2. @@toStringTag data property on the JSON / Math namespace objects
//      ("JSON" / "Math"; writable:false, enumerable:false, configurable:true).
//   3. String.prototype.split / replace @@-protocol dispatch: before
//      ToString(this), Get(arg, @@split)/@@replace and Call it when present.
//   4. Subclassing %Date% (super() creates a [[DateValue]] instance from the
//      subclass new.target) and %Symbol% (a valid `extends` value whose super()
//      throws TypeError, since the Symbol constructor rejects a NewTarget).
//
// Disposition:
//   * TraceEqual — sem must emit a trace byte-for-byte equal to the Node
//     driver's (a wrong trace is gate-fatal).
//
// The plain inline test below reduces each cluster to a boolean-valued case
// runnable without Node. The env-gated `..._vs_node` test runs the exact pinned
// files through BOTH sem and the Node trace driver and requires trace-equality.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use trust_js_sem::{evaluate_case, evaluate_case_opts, SemOutcome};
use trust_js_trace::{extract_trace, traces_equal, Completion, ProjectedValue};

// Default corpus root: <repo>/build/js262/test262-<pinned rev>. Derived from
// CARGO_MANIFEST_DIR so it works in any checkout; override with
// TRUST_JS262_CORPUS.
const DEFAULT_CORPUS: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../build/js262/test262-9e61c12835c5e4a3bdba93850427e6742c4f64c4"
);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Disp {
    /// sem must emit a trace byte-for-byte equal to the Node driver's.
    TraceEqual,
}

/// Every unique divergent file with its ruled disposition. Modes (bare/strict)
/// are derived from each file's frontmatter flags, exactly like the corpus
/// runners, so onlyStrict / noStrict cases run only their applicable mode. The
/// 21 files expand to the 38 recorded divergent runs.
const PINS: &[(&str, Disp)] = &[
    // -- Cluster 2: @@toStringTag on JSON / Math -----------------------------
    ("test/built-ins/JSON/Symbol.toStringTag.js", Disp::TraceEqual),
    ("test/built-ins/Math/Symbol.toStringTag.js", Disp::TraceEqual),
    // -- Cluster 1: symbol-keyed properties through Object operations --------
    (
        "test/built-ins/Object/freeze/frozen-object-contains-symbol-properties-non-strict.js",
        Disp::TraceEqual,
    ),
    (
        "test/built-ins/Object/freeze/frozen-object-contains-symbol-properties-strict.js",
        Disp::TraceEqual,
    ),
    (
        "test/built-ins/Object/getOwnPropertyDescriptors/symbols-included.js",
        Disp::TraceEqual,
    ),
    (
        "test/built-ins/Object/getOwnPropertySymbols/non-object-argument-valid.js",
        Disp::TraceEqual,
    ),
    (
        "test/built-ins/Object/seal/symbol-object-contains-symbol-properties-non-strict.js",
        Disp::TraceEqual,
    ),
    (
        "test/built-ins/Object/seal/symbol-object-contains-symbol-properties-strict.js",
        Disp::TraceEqual,
    ),
    (
        "test/language/expressions/assignment/dstr/obj-rest-order.js",
        Disp::TraceEqual,
    ),
    (
        "test/language/statements/for-of/dstr/obj-rest-order.js",
        Disp::TraceEqual,
    ),
    // -- Cluster 3: split / replace @@-protocol dispatch ---------------------
    (
        "test/built-ins/String/prototype/replace/cstm-replace-get-err.js",
        Disp::TraceEqual,
    ),
    (
        "test/built-ins/String/prototype/replace/cstm-replace-invocation.js",
        Disp::TraceEqual,
    ),
    (
        "test/built-ins/String/prototype/split/cstm-split-get-err.js",
        Disp::TraceEqual,
    ),
    (
        "test/built-ins/String/prototype/split/cstm-split-invocation.js",
        Disp::TraceEqual,
    ),
    (
        "test/built-ins/String/prototype/split/this-value-tostring-error.js",
        Disp::TraceEqual,
    ),
    // -- Cluster 4: subclassing Date / Symbol --------------------------------
    (
        "test/language/expressions/class/subclass-builtins/subclass-Date.js",
        Disp::TraceEqual,
    ),
    (
        "test/language/statements/class/subclass-builtins/subclass-Date.js",
        Disp::TraceEqual,
    ),
    (
        "test/language/statements/class/subclass/builtin-objects/Date/regular-subclassing.js",
        Disp::TraceEqual,
    ),
    (
        "test/language/statements/class/subclass/builtin-objects/Date/super-must-be-called.js",
        Disp::TraceEqual,
    ),
    (
        "test/language/statements/class/subclass/builtin-objects/Symbol/new-symbol-with-super-throws.js",
        Disp::TraceEqual,
    ),
    (
        "test/language/statements/class/subclass/builtin-objects/Symbol/symbol-valid-as-extends-value.js",
        Disp::TraceEqual,
    ),
];

fn completion_of(o: SemOutcome) -> Completion {
    match o {
        SemOutcome::Trace(t) => t.completion,
        SemOutcome::NoCoverage { reason } => panic!("unexpected NoCoverage: {reason}"),
    }
}

/// The `true` boolean completion (a snippet reduced to a single spec-truth).
fn assert_true(src: &str) {
    assert_eq!(
        completion_of(evaluate_case(&[], src)),
        Completion::Normal {
            v: Some(ProjectedValue::Bool { v: true })
        },
        "expected `true` completion for: {src}"
    );
}

// ---------------------------------------------------------------------------
// Plain inline tests (no Node): a boolean-reduced case for every fix.
// ---------------------------------------------------------------------------

#[test]
fn cluster1_symbol_keys_through_object_ops() {
    // freeze locks symbol-keyed own data props (non-writable + non-config).
    assert_true(
        "var s = Symbol(); var o = {}; o[s] = 1; Object.freeze(o); o[s] = 2; \
         o[s] === 1 && (delete o[s]) === false;",
    );
    // seal makes symbol-keyed props non-configurable (still writable), and a
    // sealed object rejects new symbol keys.
    assert_true(
        "var a = Symbol('A'), b = Symbol('B'); var o = {}; o[a] = 1; Object.seal(o); \
         o[a] = 2; o[b] = 1; \
         o[a] === 2 && (delete o[a]) === false && o[b] === undefined;",
    );
    // getOwnPropertyDescriptors includes symbol keys.
    assert_true(
        "var s1 = Symbol(), s2 = Symbol(); var o = { k: 1 }; o[s1] = 2; \
         Object.defineProperty(o, s2, { value: 3, writable: true, enumerable: false, configurable: true }); \
         var r = Object.getOwnPropertyDescriptors(o); \
         Object.keys(r).length === 1 && Object.getOwnPropertySymbols(r).length === 2 \
         && r[s1].value === 2 && r[s2].enumerable === false;",
    );
    // getOwnPropertySymbols(primitive) → ToObject → empty list, not TypeError.
    assert_true(
        "Object.getOwnPropertySymbols(true).length === 0 \
         && Object.getOwnPropertySymbols(1).length === 0 \
         && Object.getOwnPropertySymbols('').length === 0 \
         && Object.getOwnPropertySymbols(Symbol()).length === 0;",
    );
    // Object REST copies enumerable symbol keys in [[OwnPropertyKeys]] order
    // (integer, string-insertion, symbol-insertion).
    assert_true(
        "var calls = []; \
         var o = { get z() { calls.push('z') }, get a() { calls.push('a') } }; \
         Object.defineProperty(o, 1, { get: function() { calls.push('1') }, enumerable: true }); \
         Object.defineProperty(o, Symbol('foo'), { get: function() { calls.push('S') }, enumerable: true }); \
         var rest; ({...rest} = o); \
         calls.join(',') === '1,z,a,S' && Object.keys(rest).length === 3;",
    );
}

#[test]
fn cluster2_json_math_to_string_tag() {
    assert_true("JSON[Symbol.toStringTag] === 'JSON';");
    assert_true("Math[Symbol.toStringTag] === 'Math';");
    // The descriptor is non-writable, non-enumerable, configurable.
    assert_true(
        "var d = Object.getOwnPropertyDescriptor(JSON, Symbol.toStringTag); \
         d.value === 'JSON' && d.writable === false && d.enumerable === false && d.configurable === true;",
    );
    assert_true(
        "var d = Object.getOwnPropertyDescriptor(Math, Symbol.toStringTag); \
         d.value === 'Math' && d.writable === false && d.enumerable === false && d.configurable === true;",
    );
}

#[test]
fn cluster3_split_replace_at_at_protocol() {
    // split dispatches to @@split (Call(m, sep, «O, limit»)).
    assert_true(
        "var sep = {}, rv = {}, got; \
         sep[Symbol.split] = function() { got = arguments; return rv; }; \
         var r = ''.split(sep, 'limit'); \
         r === rv && got.length === 2 && got[0] === '' && got[1] === 'limit';",
    );
    // replace dispatches to @@replace (Call(m, search, «O, replaceValue»)).
    assert_true(
        "var search = {}, rv = {}, got, self; \
         search[Symbol.replace] = function() { self = this; got = arguments; return rv; }; \
         var r = ''.replace(search, 'replace value'); \
         r === rv && self === search && got.length === 2 && got[0] === '' && got[1] === 'replace value';",
    );
    // A throwing @@split getter propagates (GetMethod is abrupt).
    assert_true(
        "var p = {}; Object.defineProperty(p, Symbol.split, { get: function() { throw 7; } }); \
         var t; try { ''.split(p); } catch (e) { t = e; } t === 7;",
    );
    // this-value ToString is NOT called when the separator has an @@split; it
    // IS called (before separator processing) otherwise.
    assert_true(
        "var recv = {}; recv.toString = function() { throw 1; }; \
         var withSplit = {}; withSplit[Symbol.split] = function() { return 'ok'; }; \
         var noThrow = String.prototype.split.call(recv, withSplit, Symbol()) === 'ok'; \
         var sep = {}; \
         sep[Symbol.toPrimitive] = function() { throw 2; }; \
         var t = false; \
         try { String.prototype.split.call(recv, sep, Symbol()); } catch (e) { t = (e === 1); } \
         noThrow && t;",
    );
}

#[test]
fn cluster4_subclassing_date_and_symbol() {
    // `class extends Date {}`: super() runs the driver's Date wrapper, whose
    // `return new RealDate(...)` discards the subclass new.target — so the
    // instance is parented on %Date.prototype% (NOT the subclass prototype):
    // `sub instanceof Date` is true but `sub instanceof Sub` is false. (The
    // subclass-Date.js file's `assert(sub instanceof Sub)` therefore throws
    // Test262Error under the oracle — verified equal in the vs_node test.)
    assert_true(
        "var Sub = class extends Date {}; var sub = new Sub(0); \
         sub instanceof Date && !(sub instanceof Sub) && sub.getTime() === 0;",
    );
    // The multi-argument Date form works on a subclass instance.
    assert_true(
        "class D extends Date {} var d = new D(1859, '10', 24, 11); \
         d.getFullYear() === 1859 && d.getMonth() === 10 && d.getDate() === 24;",
    );
    // A derived Date constructor that never calls super() has an unbound `this`
    // (ReferenceError); one that calls super(d) initializes the slot.
    assert_true(
        "class D extends Date { constructor() {} } \
         var t = false; try { new D(0); } catch (e) { t = e instanceof ReferenceError; } \
         class D2 extends Date { constructor(d) { super(d); } } \
         t && new D2(0).getTime() === 0;",
    );
    // `class extends Symbol {}` is a valid definition.
    assert_true("class S extends Symbol {} typeof S === 'function';");
    // ...but `new` on it throws TypeError (Symbol rejects a NewTarget), whether
    // the default or an explicit super()-calling constructor.
    assert_true(
        "class S1 extends Symbol {} \
         class S2 extends Symbol { constructor() { super(); } } \
         var t1 = false, t2 = false; \
         try { new S1(); } catch (e) { t1 = e instanceof TypeError; } \
         try { new S2(); } catch (e) { t2 = e instanceof TypeError; } \
         t1 && t2;",
    );
}

// ---------------------------------------------------------------------------
// Frontmatter + harness plumbing (shared with the corpus runners' shape).
// ---------------------------------------------------------------------------

struct Frontmatter {
    includes: Vec<String>,
    flags: Vec<String>,
}

fn parse_frontmatter(body: &str) -> Frontmatter {
    let fm = body
        .split_once("/*---")
        .and_then(|(_, rest)| rest.split_once("---*/"))
        .map_or("", |(fm, _)| fm);
    let mut includes = Vec::new();
    let mut flags = Vec::new();
    let mut lines = fm.lines().peekable();
    while let Some(line) = lines.next() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("includes:") {
            let rest = rest.trim();
            if let Some(inner) = rest.strip_prefix('[') {
                let inner = inner.trim_end_matches(']');
                includes.extend(
                    inner
                        .split(',')
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty()),
                );
            } else {
                while let Some(next) = lines.peek() {
                    let nt = next.trim_start();
                    if let Some(item) = nt.strip_prefix("- ") {
                        includes.push(item.trim().to_string());
                        lines.next();
                    } else {
                        break;
                    }
                }
            }
        } else if let Some(rest) = t.strip_prefix("flags:") {
            let rest = rest.trim();
            if let Some(inner) = rest.strip_prefix('[') {
                let inner = inner.trim_end_matches(']');
                flags.extend(
                    inner
                        .split(',')
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty()),
                );
            }
        }
    }
    Frontmatter { includes, flags }
}

fn modes_for(flags: &[String]) -> &'static [bool] {
    if flags.iter().any(|f| f == "onlyStrict") {
        &[true]
    } else if flags.iter().any(|f| f == "raw" || f == "noStrict") {
        &[false]
    } else {
        &[false, true]
    }
}

fn corpus_root() -> Option<PathBuf> {
    let corpus =
        PathBuf::from(std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.into()));
    corpus.join("harness/assert.js").is_file().then_some(corpus)
}

// ---------------------------------------------------------------------------
// Plain corpus sweep (no Node): each pinned file must produce a real trace
// (never a wrong NoCoverage) for its ruled disposition.
// ---------------------------------------------------------------------------

#[test]
fn pinned_s1e_divergences_local_cover() {
    let Some(corpus) = corpus_root() else {
        eprintln!("SKIP pinned_s1e_divergences_local_cover: corpus not present");
        return;
    };
    let mut include_cache: std::collections::HashMap<String, String> =
        std::collections::HashMap::new();
    let mut failures = Vec::new();
    let mut checked = 0u64;

    for (rel, disp) in PINS {
        let path = corpus.join(rel);
        let body = match std::fs::read_to_string(&path) {
            Ok(b) => b,
            Err(e) => {
                failures.push(format!("{rel}: read failed: {e}"));
                continue;
            }
        };
        let fm = parse_frontmatter(&body);
        let raw = fm.flags.iter().any(|f| f == "raw");
        let mut include_names: Vec<String> = if raw {
            Vec::new()
        } else {
            vec!["assert.js".into(), "sta.js".into()]
        };
        include_names.extend(fm.includes.iter().cloned());
        let mut include_srcs = Vec::new();
        for name in &include_names {
            let src = include_cache.entry(name.clone()).or_insert_with(|| {
                std::fs::read_to_string(corpus.join("harness").join(name)).expect("read include")
            });
            include_srcs.push(src.clone());
        }
        let inc_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();

        for &strict in modes_for(&fm.flags) {
            checked += 1;
            let sem_body = if strict {
                format!("\"use strict\";\n{body}")
            } else {
                body.clone()
            };
            let out = evaluate_case_opts(&inc_refs, &sem_body, false);
            let mode = if strict { "strict" } else { "bare" };
            let ok = match disp {
                // Covered = a concrete trace (never a NoCoverage refusal, never
                // a panic). The completion may be Normal (assert-passing tests)
                // or a Throw (subclass-Date.js's `instanceof` assert fails under
                // the driver's Date wrapper). The vs_node test checks equality.
                Disp::TraceEqual => matches!(&out, SemOutcome::Trace(_)),
            };
            if !ok {
                failures.push(format!("{rel} [{mode}]: expected covered trace, got {out:?}"));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "pinned s1e local cover ({} of {checked} checks failed):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Env-gated differential vs the Node trace driver.
// ---------------------------------------------------------------------------

#[test]
#[allow(clippy::too_many_lines)]
fn pinned_s1e_divergences_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP pinned_s1e_divergences_vs_node: set TRUST_JS_NODE to run");
        return;
    };
    let Some(corpus) = corpus_root() else {
        eprintln!("SKIP pinned_s1e_divergences_vs_node: corpus not present");
        return;
    };
    let driver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs");
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut include_cache: std::collections::HashMap<String, String> =
        std::collections::HashMap::new();
    let mut failures: Vec<String> = Vec::new();
    let mut equal = 0u64;
    let mut case_no = 0usize;

    for (rel, disp) in PINS {
        let path = corpus.join(rel);
        let body = std::fs::read_to_string(&path).expect("read pinned case");
        let fm = parse_frontmatter(&body);
        let raw = fm.flags.iter().any(|f| f == "raw");
        let mut include_names: Vec<String> = if raw {
            Vec::new()
        } else {
            vec!["assert.js".into(), "sta.js".into()]
        };
        include_names.extend(fm.includes.iter().cloned());
        let mut include_srcs = Vec::new();
        let mut include_paths = Vec::new();
        for name in &include_names {
            let p = corpus.join("harness").join(name);
            let src = include_cache
                .entry(name.clone())
                .or_insert_with(|| std::fs::read_to_string(&p).expect("read include"));
            include_srcs.push(src.clone());
            include_paths.push(p.display().to_string());
        }
        let inc_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();

        for &strict in modes_for(&fm.flags) {
            case_no += 1;
            let mode = if strict { "strict" } else { "bare" };
            let sem_body = if strict {
                format!("\"use strict\";\n{body}")
            } else {
                body.clone()
            };
            let sem = evaluate_case_opts(&inc_refs, &sem_body, false);

            let sem_trace = match (disp, sem) {
                (Disp::TraceEqual, SemOutcome::Trace(t)) => t,
                (Disp::TraceEqual, SemOutcome::NoCoverage { reason }) => {
                    failures.push(format!(
                        "{rel} [{mode}]: expected covered trace, got NoCoverage: {reason}"
                    ));
                    continue;
                }
            };

            let body_path = tmp.path().join(format!("pin-{case_no}.body.js"));
            std::fs::write(&body_path, &body).expect("write body");
            let manifest = serde_json::json!({
                "completion_witness": false,
                "includes": include_paths,
                "source": body_path.display().to_string(),
                "mode": mode,
                "kind": "script",
            });
            let manifest_path = tmp.path().join(format!("pin-{case_no}.manifest.json"));
            let mut mf = std::fs::File::create(&manifest_path).expect("create manifest");
            mf.write_all(manifest.to_string().as_bytes())
                .expect("write manifest");
            drop(mf);

            let out = Command::new(&node)
                .arg(&driver)
                .arg(&manifest_path)
                .env("TZ", "UTC")
                .env("LANG", "C")
                .env("LC_ALL", "C")
                .output()
                .expect("spawn node driver");
            let node_trace = match extract_trace(&out.stdout) {
                Ok(t) => t,
                Err(e) => {
                    failures.push(format!(
                        "{rel} [{mode}]: node trace extraction failed: {e} (stderr: {})",
                        String::from_utf8_lossy(&out.stderr)
                    ));
                    continue;
                }
            };
            if traces_equal(&sem_trace, &node_trace) {
                equal += 1;
            } else {
                failures.push(format!(
                    "{rel} [{mode}]: WRONG TRACE\n  sem:  {:?}\n  node: {:?}",
                    sem_trace.completion, node_trace.completion
                ));
            }
        }
    }

    eprintln!("== pinned s1e divergences: {equal} node-equal traces ==");
    assert!(
        failures.is_empty(),
        "pinned s1e divergence failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
