// Pinned regression for the S1F2 gate's %TypedArray%.prototype divergence
// cluster (20 cases / 40 runs): methods that begin with ValidateTypedArray
// must throw a TypeError when `this` is a resizable-buffer view that shrank
// out of bounds (or is detached); `set` must throw that TypeError before the
// srcLength+offset RangeError; `includes` must short-circuit on [[ArrayLength]]
// == 0 BEFORE coercing fromIndex; a saturating srcLength+offset compare must
// not overflow (offset == +Infinity); and the integer-indexed exotic [[Set]]
// with a distinct Receiver must shadow onto the receiver instead of reaching
// the %TypedArray%.prototype accessor.
//
// Each pinned case is either byte-for-byte trace-equal with the Node driver
// (Cover) or a sound NoCoverage (Refuse, e.g. the Proxy-bearing tail); a
// WRONG trace is never acceptable. Gated on TRUST_JS_NODE (+ optional
// TRUST_JS262_CORPUS).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use trust_js_sem::{evaluate_case_opts, SemOutcome};
use trust_js_trace::{explain_divergence, extract_trace, traces_equal};

// Default corpus root: <repo>/build/js262/test262-<pinned rev>. Derived from
// CARGO_MANIFEST_DIR so it works in any checkout; override with
// TRUST_JS262_CORPUS.
const DEFAULT_CORPUS: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../build/js262/test262-9e61c12835c5e4a3bdba93850427e6742c4f64c4"
);

// The 20 gate-divergent cases (each run bare + strict = 40 runs).
const CASES: &[&str] = &[
    "test/built-ins/TypedArray/prototype/at/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/entries/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/every/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/fill/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/find/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/findIndex/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/forEach/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/includes/length-zero-returns-false.js",
    "test/built-ins/TypedArray/prototype/includes/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/indexOf/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/join/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/keys/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/lastIndexOf/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/reverse/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/set/typedarray-arg-src-range-greather-than-target-throws-rangeerror.js",
    "test/built-ins/TypedArray/prototype/set/typedarray-arg-target-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/slice/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/some/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArray/prototype/values/return-abrupt-from-this-out-of-bounds.js",
    "test/built-ins/TypedArrayConstructors/internals/Set/key-is-valid-index-prototype-chain-set.js",
];

fn node_bin() -> Option<String> {
    std::env::var("TRUST_JS_NODE").ok()
}

fn driver_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs")
}

fn parse_includes(body: &str) -> Vec<String> {
    let fm = body
        .split_once("/*---")
        .and_then(|(_, rest)| rest.split_once("---*/"))
        .map_or("", |(fm, _)| fm);
    let mut includes = Vec::new();
    let mut lines = fm.lines().peekable();
    while let Some(line) = lines.next() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("includes:") {
            let rest = rest.trim();
            if let Some(inner) = rest.strip_prefix('[') {
                includes.extend(
                    inner
                        .trim_end_matches(']')
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
                    } else if nt.is_empty() || nt.starts_with('-') {
                        lines.next();
                    } else {
                        break;
                    }
                }
            }
        }
    }
    includes
}

#[allow(clippy::too_many_arguments)]
fn node_trace_of(
    node: &str,
    driver: &Path,
    tmp: &Path,
    tag: &str,
    body_path: &str,
    include_paths: &[String],
    strict: bool,
) -> Result<trust_js_trace::ObservableTrace, String> {
    let manifest = serde_json::json!({
        "completion_witness": false,
        "includes": include_paths,
        "source": body_path,
        "mode": if strict { "strict" } else { "bare" },
        "kind": "script",
    });
    let manifest_path = tmp.join(format!("{tag}.manifest.json"));
    let mut mf = std::fs::File::create(&manifest_path).expect("create manifest");
    mf.write_all(manifest.to_string().as_bytes()).expect("write manifest");
    drop(mf);
    let out = Command::new(node)
        .arg(driver)
        .arg(&manifest_path)
        .env("TZ", "UTC")
        .env("LANG", "C")
        .env("LC_ALL", "C")
        .output()
        .expect("spawn node driver");
    extract_trace(&out.stdout).map_err(|e| {
        format!(
            "node trace extraction failed: {e} (stderr: {})",
            String::from_utf8_lossy(&out.stderr)
        )
    })
}

#[test]
#[allow(clippy::too_many_lines)]
fn typed_array_oob_cluster_vs_node() {
    let Some(node) = node_bin() else {
        eprintln!("SKIP typed_array_oob_cluster_vs_node: set TRUST_JS_NODE (+ optional TRUST_JS262_CORPUS) to run");
        return;
    };
    let corpus =
        PathBuf::from(std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.into()));
    assert!(
        corpus.join("harness/assert.js").is_file(),
        "corpus harness not found under {}",
        corpus.display()
    );
    let driver = driver_path();
    let tmp = tempfile::tempdir().expect("tempdir");

    let mut failures: Vec<String> = Vec::new();
    let (mut cover, mut refuse) = (0u64, 0u64);

    for (ci, rel) in CASES.iter().enumerate() {
        let path = corpus.join(rel);
        let body = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read pinned case {rel}: {e}"));

        let mut include_names = vec!["assert.js".to_string(), "sta.js".to_string()];
        include_names.extend(parse_includes(&body));
        let mut include_srcs: Vec<String> = Vec::new();
        let mut include_paths: Vec<String> = Vec::new();
        for name in &include_names {
            let p = corpus.join("harness").join(name);
            assert!(p.is_file(), "missing harness include {name} for {rel}");
            include_srcs.push(std::fs::read_to_string(&p).expect("read include"));
            include_paths.push(p.display().to_string());
        }

        // Write the body once for the node driver.
        let body_path = tmp.path().join(format!("case-{ci}.body.js"));
        std::fs::write(&body_path, &body).expect("write body");

        for &strict in &[false, true] {
            let mode = if strict { "strict" } else { "bare" };
            let sem_body = if strict {
                format!("\"use strict\";\n{body}")
            } else {
                body.clone()
            };
            let inc_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();
            let sem = evaluate_case_opts(&inc_refs, &sem_body, false);
            let sem_trace = match sem {
                SemOutcome::NoCoverage { reason } => {
                    // Sound refusal (e.g. the Proxy tail) is never a wrong trace.
                    eprintln!("REFUSE {rel} [{mode}]: {reason}");
                    refuse += 1;
                    continue;
                }
                SemOutcome::Trace(t) => t,
            };
            let node_trace = match node_trace_of(
                &node,
                &driver,
                tmp.path(),
                &format!("case-{ci}-{mode}"),
                &body_path.display().to_string(),
                &include_paths,
                strict,
            ) {
                Ok(t) => t,
                Err(e) => {
                    failures.push(format!("{rel} [{mode}]: {e}"));
                    continue;
                }
            };
            if traces_equal(&sem_trace, &node_trace) {
                cover += 1;
            } else {
                failures.push(format!(
                    "{rel} [{mode}]: WRONG TRACE: {}",
                    explain_divergence(&sem_trace, &node_trace)
                        .unwrap_or_else(|| "unlocalized".into())
                ));
            }
        }
    }

    eprintln!("== typed-array OOB cluster: cover {cover} / refuse {refuse} (of 40 runs) ==");
    assert!(
        failures.is_empty(),
        "typed-array OOB cluster wrong traces ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// Focused Cover micro-pins for the three non-shared root causes, written so
// they never touch the harness's Array.from / Proxy dependencies (so they
// prove exact trace-equality rather than settling for a sound refusal).
const MICRO: &[(&str, &str)] = &[
    // Fix C: includes short-circuits on [[ArrayLength]] == 0 BEFORE coercing
    // fromIndex (its valueOf must not run).
    (
        "includes-len0-no-fromindex-coerce",
        "var touched = false;\n\
         var fi = { valueOf: function(){ touched = true; return 0; } };\n\
         var s = new Int8Array(0);\n\
         console.log(s.includes(0), s.includes(), s.includes(0, fi), touched);",
    ),
    // Fix E: set with a +Infinity offset is a RangeError, not an overflow panic.
    (
        "set-infinity-offset-rangeerror",
        "var t = new Int16Array(2), src = new Int16Array(2);\n\
         var err;\n\
         try { t.set(src, Infinity); } catch (e) { err = e.constructor.name; }\n\
         console.log(err);",
    ),
    // Fix D: integer-indexed exotic [[Set]] through the prototype chain with a
    // distinct receiver shadows onto the receiver (uncoerced) and never reaches
    // a %TypedArray%.prototype accessor.
    (
        "receiver-set-shadows-index",
        "Object.defineProperty(Int8Array.prototype, 0, {\n\
           get: function(){ throw new Error('g'); },\n\
           set: function(){ throw new Error('s'); },\n\
           configurable: true });\n\
         var target = new Int8Array([7]);\n\
         var receiver = Object.create(target);\n\
         var coerced = 0;\n\
         var value = { valueOf: function(){ coerced++; return 2; } };\n\
         receiver[0] = value;\n\
         console.log(target[0], receiver[0] === value, coerced);\n\
         delete Int8Array.prototype[0];",
    ),
    // Fix A (direct): a shrunk-out-of-bounds view makes join/reverse/at throw a
    // TypeError via ValidateTypedArray.
    (
        "oob-view-methods-typeerror",
        "var ab = new ArrayBuffer(8, {maxByteLength: 16});\n\
         var a = new Int16Array(ab, 2, 2);\n\
         ab.resize(3);\n\
         function tag(f){ try { f(); return 'no-throw'; } catch (e) { return e.constructor.name; } }\n\
         console.log(tag(function(){ a.at(0); }), tag(function(){ a.join(); }), tag(function(){ a.reverse(); }), tag(function(){ a.includes(0); }));",
    ),
];

#[test]
fn typed_array_oob_micro_vs_node() {
    let Some(node) = node_bin() else {
        eprintln!("SKIP typed_array_oob_micro_vs_node: set TRUST_JS_NODE to run");
        return;
    };
    let driver = driver_path();
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();

    for (name, body) in MICRO {
        for &strict in &[false, true] {
            let mode = if strict { "strict" } else { "bare" };
            let sem_body = if strict {
                format!("\"use strict\";\n{body}")
            } else {
                (*body).to_string()
            };
            let sem_trace = match evaluate_case_opts(&[], &sem_body, false) {
                SemOutcome::Trace(t) => t,
                SemOutcome::NoCoverage { reason } => {
                    failures.push(format!("{name} [{mode}]: unexpected NoCoverage: {reason}"));
                    continue;
                }
            };
            let body_path = tmp.path().join(format!("micro-{name}-{mode}.js"));
            std::fs::write(&body_path, body).expect("write body");
            let node_trace = match node_trace_of(
                &node,
                &driver,
                tmp.path(),
                &format!("micro-{name}-{mode}"),
                &body_path.display().to_string(),
                &[],
                strict,
            ) {
                Ok(t) => t,
                Err(e) => {
                    failures.push(format!("{name} [{mode}]: {e}"));
                    continue;
                }
            };
            if !traces_equal(&sem_trace, &node_trace) {
                failures.push(format!(
                    "{name} [{mode}]: WRONG TRACE: {}",
                    explain_divergence(&sem_trace, &node_trace)
                        .unwrap_or_else(|| "unlocalized".into())
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "typed-array OOB micro-pin failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
