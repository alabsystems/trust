// Adversarial + corpus differential for async methods, array/call spread, and
// Array.from / Array.of. Every covered case must be byte-for-byte trace-equal
// with the Node driver; a refusal is sound and counted; a WRONG trace or a
// PANIC is fatal. The adversarial minis pin exact spec corners (async method
// returns a promise + await interleaving, spread iteration order + hole
// handling + trailing comma, IteratorClose on a mapFn throw, Array.from over
// iterables / array-likes / mapFn / thisArg, Array.of); the corpus sweep is the
// byte-for-byte arbiter over the class/object async-method and spread and
// Array.from/of directories.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::BTreeMap;
use std::io::Write;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::process::Command;
use trust_js_sem::{evaluate_case_opts, SemOutcome};
use trust_js_trace::{explain_divergence, extract_trace, traces_equal, ObservableTrace};

// Default corpus root: <repo>/build/js262/test262-<pinned rev>. Derived from
// CARGO_MANIFEST_DIR so it works in any checkout; override with
// TRUST_JS262_CORPUS.
const DEFAULT_CORPUS: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../build/js262/test262-9e61c12835c5e4a3bdba93850427e6742c4f64c4"
);

fn node_bin() -> Option<String> {
    std::env::var("TRUST_JS_NODE").ok()
}

fn corpus_root() -> PathBuf {
    PathBuf::from(std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string()))
}

fn driver_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs")
}

/// Run one bare body (no harness includes) through the Node driver, returning
/// its trace.
fn node_trace(node: &str, driver: &Path, tmp: &Path, tag: &str, body: &str) -> ObservableTrace {
    let body_path = tmp.join(format!("{tag}.body.js"));
    std::fs::write(&body_path, body).expect("write body");
    let empty_includes: Vec<String> = Vec::new();
    let manifest = serde_json::json!({
        "completion_witness": false,
        "includes": empty_includes,
        "source": body_path.display().to_string(),
        "mode": "bare",
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
    extract_trace(&out.stdout).unwrap_or_else(|e| {
        panic!(
            "node trace extraction failed for {tag}: {e} (stderr: {})",
            String::from_utf8_lossy(&out.stderr)
        )
    })
}

/// The adversarial minis. Each MUST be exactly trace-equal with Node (never a
/// refusal — these pin behavior we now implement).
const MINIS: &[(&str, &str)] = &[
    // ---- async methods -------------------------------------------------
    (
        "obj_async_method_returns_promise",
        "var o = { async m() { return 42; } }; var p = o.m(); \
         console.log(p instanceof Promise, Object.getPrototypeOf(o.m).constructor === undefined); \
         p.then(v => console.log('resolved', v));",
    ),
    (
        "obj_async_method_await_ordering",
        "var o = { async m() { console.log(1); await 0; console.log(2); await 0; console.log(4); } }; \
         o.m(); console.log(3); Promise.resolve().then(()=>console.log('micro'));",
    ),
    (
        "class_async_method",
        "class C { async m(x) { return x * 2; } } var c = new C(); \
         c.m(21).then(v => console.log('got', v));",
    ),
    (
        "class_static_async_method",
        "class C { static async m() { return 'S'; } } C.m().then(v => console.log(v));",
    ),
    (
        "async_method_super",
        "class A { greet() { return 'A'; } } \
         class B extends A { async greet() { return 'B+' + super.greet(); } } \
         new B().greet().then(v => console.log(v));",
    ),
    (
        "async_method_this",
        "var o = { v: 7, async m() { return this.v; } }; o.m().then(v => console.log(v));",
    ),
    (
        "async_method_computed_key",
        "var k = 'go'; var o = { async [k]() { return 1; } }; o.go().then(v => console.log(v));",
    ),
    (
        "async_method_throw_rejects",
        "var o = { async m() { throw new TypeError('x'); } }; \
         o.m().then(()=>console.log('no'), e => console.log('rej', e.name));",
    ),
    (
        "async_method_name_prop",
        "var o = { async foo() {} }; console.log(o.foo.name, o.foo.length);",
    ),
    (
        "async_method_not_constructor",
        "var o = { async m() {} }; try { new o.m(); console.log('no'); } catch (e) { console.log(e.name); }",
    ),
    (
        "async_method_await_thenable",
        "var t = { then(res) { res(99); } }; \
         var o = { async m() { var v = await t; console.log('awaited', v); return v; } }; \
         o.m().then(v => console.log('final', v));",
    ),
    // ---- array-literal spread ------------------------------------------
    ("spread_array_basic", "console.log([...[1,2,3]]);"),
    ("spread_array_mid", "console.log([0, ...[1,2], 3]);"),
    ("spread_array_multiple", "console.log([...[1,2], ...[3,4]]);"),
    ("spread_string", "console.log([...'abc']);"),
    ("spread_string_astral", "console.log([...'a\\u{1f600}b'].length);"),
    ("spread_set", "console.log([...new Set([1,1,2,3,3])]);"),
    (
        "spread_map",
        "var m = new Map([['a',1],['b',2]]); console.log([...m]);",
    ),
    (
        "spread_generator",
        "function* g() { yield 1; yield 2; yield 3; } console.log([...g()]);",
    ),
    (
        "spread_iteration_order",
        "var log = []; var it = { [Symbol.iterator]() { var i = 0; return { next() { log.push('n' + i); return i < 3 ? {value: i++, done: false} : {value: undefined, done: true}; } }; } }; \
         var a = [...it]; console.log(a, log.join(','));",
    ),
    ("spread_trailing_comma", "console.log([...[1,2],]);"),
    ("spread_elision_after", "console.log([...[1,2],,].length);"),
    ("spread_with_holes", "console.log([1, , ...[2,3], , 4].length);"),
    ("spread_empty", "console.log([...[]].length, [...''].length);"),
    (
        "spread_user_iterator_close_not_called",
        "var closed = false; var it = { [Symbol.iterator]() { var i=0; return { next(){ return i<2?{value:i++,done:false}:{value:undefined,done:true}; }, return(){ closed=true; return {}; } }; } }; \
         var a = [...it]; console.log(a, closed);",
    ),
    // ---- call / new spread ---------------------------------------------
    (
        "call_spread_basic",
        "function f(a,b,c){ return a+b+c; } console.log(f(...[1,2,3]));",
    ),
    (
        "call_spread_mixed",
        "function f(){ return Array.prototype.slice.call(arguments); } console.log(f(1, ...[2,3], 4, ...[5]));",
    ),
    (
        "call_spread_string",
        "function f(){ return arguments.length; } console.log(f(...'hello'));",
    ),
    (
        "call_spread_this",
        "var o = { v: 5, f(x, y) { return this.v + x + y; } }; console.log(o.f(...[10, 20]));",
    ),
    (
        "new_spread",
        "function P(a,b){ this.s = a + b; } console.log(new P(...[3,4]).s);",
    ),
    (
        "call_spread_set",
        "console.log(Math.max(...new Set([3,1,4,1,5,9,2,6])));",
    ),
    ("call_spread_trailing_comma", "function f(a,b){return a+b;} console.log(f(...[2,3],));"),
    (
        "call_spread_order",
        "var log=[]; function side(x){ log.push(x); return x; } function f(){ return Array.prototype.slice.call(arguments).join(','); } \
         var r = f(side('a'), ...[side('b'),side('c')], side('d')); console.log(r, log.join(','));",
    ),
    // ---- Array.from ----------------------------------------------------
    ("from_array", "console.log(Array.from([1,2,3]));"),
    ("from_string", "console.log(Array.from('abc'));"),
    ("from_set", "console.log(Array.from(new Set([1,2,2,3])));"),
    (
        "from_map",
        "console.log(Array.from(new Map([['x',1]])));",
    ),
    (
        "from_generator",
        "function* g(){ yield 10; yield 20; } console.log(Array.from(g()));",
    ),
    (
        "from_arraylike",
        "console.log(Array.from({ length: 3, 0: 'a', 1: 'b', 2: 'c' }));",
    ),
    (
        "from_arraylike_holes",
        "console.log(Array.from({ length: 3, 0: 'a', 2: 'c' }));",
    ),
    (
        "from_mapfn",
        "console.log(Array.from([1,2,3], x => x * x));",
    ),
    (
        "from_mapfn_index",
        "console.log(Array.from(['a','b','c'], (x, i) => x + i));",
    ),
    (
        "from_mapfn_thisarg",
        "var ctx = { mul: 3 }; console.log(Array.from([1,2,3], function(x){ return x * this.mul; }, ctx));",
    ),
    (
        "from_mapfn_over_iterable",
        "function* g(){ yield 1; yield 2; } console.log(Array.from(g(), x => x + 100));",
    ),
    (
        "from_empty",
        "console.log(Array.from([]).length, Array.from('').length, Array.from({length:0}).length);",
    ),
    (
        "from_number_not_iterable",
        "console.log(Array.from(5).length, Array.from(true).length);",
    ),
    (
        "from_undefined_throws",
        "try { Array.from(undefined); console.log('no'); } catch(e){ console.log(e.name); }",
    ),
    (
        "from_mapfn_not_callable",
        "try { Array.from([1], 5); console.log('no'); } catch(e){ console.log(e.name); }",
    ),
    (
        "from_mapfn_throws_closes",
        "var closed=false; var it={ [Symbol.iterator](){ var i=0; return { next(){ return i<3?{value:i++,done:false}:{done:true}; }, return(){ closed=true; return {}; } }; } }; \
         try { Array.from(it, x => { if (x===1) throw new RangeError('stop'); return x; }); } catch(e){ console.log(e.name, closed); }",
    ),
    (
        "from_length_prop",
        "console.log(Array.from({length:2, 0:'p', 1:'q'}).length);",
    ),
    // ---- Array.of ------------------------------------------------------
    ("of_basic", "console.log(Array.of(1,2,3));"),
    ("of_single_number", "console.log(Array.of(7).length, Array.of(7)[0]);"),
    ("of_empty", "console.log(Array.of().length);"),
    ("of_holes_semantics", "console.log(Array.of(undefined, undefined).length);"),
    ("of_mixed", "console.log(Array.of(1, 'a', true, null));"),
    // ---- Array.from/of with a detached (non-constructor) receiver ------
    (
        "from_detached_receiver",
        "var f = Array.from; console.log(f([1,2,3]));",
    ),
    (
        "of_detached_receiver",
        "var of = Array.of; console.log(of(1,2,3));",
    ),
    (
        "from_call_null",
        "console.log(Array.from.call(null, [9,8,7]));",
    ),
    // ---- TypedArray.from / of ------------------------------------------
    ("ta_from_array", "console.log(Array.from(Int8Array.from([1,2,3])));"),
    ("ta_from_iterable", "console.log(Array.from(Uint8Array.from(new Set([10,20,30]))));"),
    ("ta_from_string_coerce", "console.log(Array.from(Float64Array.from(['1.5','2.5'])));"),
    ("ta_from_truncation", "console.log(Array.from(Int8Array.from([300, -1, 128])));"),
    // A mapFn over an ARRAY-LIKE (non-iterator) source is incremental in both
    // sem and V8 → exact. (The iterable-path mapFn corner is engine-divergent
    // and sound-refused; see the refusal pins below.)
    ("ta_from_mapfn", "console.log(Array.from(Int16Array.from({length:3, 0:1, 1:2, 2:3}, x => x * 10)));"),
    ("ta_from_arraylike", "console.log(Array.from(Uint8Array.from({length: 2, 0: 5, 1: 6})));"),
    ("ta_of_basic", "console.log(Array.from(Int32Array.of(4,5,6)));"),
    ("ta_of_empty", "console.log(Int8Array.of().length);"),
    ("ta_from_empty", "console.log(Uint8Array.from([]).length, Uint8Array.from('').length);"),
    (
        "ta_from_not_constructor",
        "try { Int8Array.from.call({}, [1]); console.log('no'); } catch(e){ console.log(e.name); }",
    ),
    (
        "ta_from_bigint_mismatch",
        "try { BigInt64Array.from([1,2,3]); console.log('no'); } catch(e){ console.log(e.name); }",
    ),
    ("ta_from_bigint_ok", "console.log(Array.from(BigInt64Array.from([1n,2n,3n]), x => Number(x)));"),
    // TypedArrayCreate step-3: a custom constructor returning a SMALLER
    // instance than requested throws TypeError (before any element set).
    (
        "ta_of_custom_smaller_throws",
        "var ctor = function(){ return new Int8Array(1); }; \
         try { Int8Array.of.call(ctor, 1, 2); console.log('no'); } catch(e){ console.log(e.name); }",
    ),
    (
        "ta_from_custom_smaller_iter_throws",
        "var ctor = function(){ return new Int8Array(1); }; \
         try { Int8Array.from.call(ctor, [1,2]); console.log('no'); } catch(e){ console.log(e.name); }",
    ),
    (
        "ta_from_custom_smaller_arraylike_throws",
        "var ctor = function(){ return new Int8Array(1); }; \
         try { Int8Array.from.call(ctor, {length: 2}); console.log('no'); } catch(e){ console.log(e.name); }",
    ),
    (
        "ta_of_bigint_custom_smaller_throws",
        "var ctor = function(){ return new BigInt64Array(1); }; \
         try { BigInt64Array.of.call(ctor, 1n, 2n); console.log('no'); } catch(e){ console.log(e.name); }",
    ),
    (
        "ta_from_bigint_custom_smaller_throws",
        "var ctor = function(){ return new BigInt64Array(1); }; \
         try { BigInt64Array.from.call(ctor, [1n, 2n]); console.log('no'); } catch(e){ console.log(e.name); }",
    ),
    // A custom constructor returning an EXACT / LARGER instance is fine.
    (
        "ta_of_custom_exact_ok",
        "var ctor = function(){ return new Int8Array(2); }; \
         console.log(Array.from(Int8Array.of.call(ctor, 5, 6)));",
    ),
    (
        "ta_of_custom_larger_ok",
        "var ctor = function(){ return new Int8Array(4); }; \
         console.log(Array.from(Int8Array.of.call(ctor, 5, 6)));",
    ),
    (
        "ta_from_custom_exact_ok",
        "var ctor = function(){ return new Uint8Array(2); }; \
         console.log(Array.from(Uint8Array.from.call(ctor, [7, 8])));",
    ),
    // ---- interactions --------------------------------------------------
    (
        "from_then_spread",
        "console.log([...Array.from(new Set([1,2,3]))]);",
    ),
    (
        "async_method_spread_args",
        "var o = { async m(...xs){ return xs.reduce((a,b)=>a+b,0); } }; o.m(...[1,2,3,4]).then(v=>console.log(v));",
    ),
];

/// Async generators (`async function*`, `async *m(){}`) and for-await stay out
/// of slice: every form must be a SOUND refusal (NoCoverage), never a wrong
/// trace. (These do not run against Node — they assert the refusal contract.)
#[test]
fn async_generators_and_for_await_refuse() {
    let cases = [
        "async function* g() { yield 1; }",
        "var g = async function*() { yield await 1; }; g();",
        "var o = { async *m() { yield 1; } };",
        "class C { async *m() { yield 1; } }",
        "class C { static async *m() { yield 1; } }",
        "async function f() { for await (const x of []) {} }",
    ];
    for src in cases {
        match evaluate_case_opts(&[], src, false) {
            SemOutcome::NoCoverage { .. } => {}
            SemOutcome::Trace(t) => {
                // A pure early-SyntaxError trace would be acceptable only if
                // Node also raised SyntaxError; async generators are valid
                // syntax, so the sound outcome is NoCoverage.
                panic!("async-gen/for-await case unexpectedly produced a trace: {src}\n{t:?}");
            }
        }
    }
}

/// Engine-divergent corners that Node 24.5 itself resolves against the current
/// spec (V8's `eval(...spread)` and `%TypedArray%.from` lazy-array read): the
/// sem must SOUND-REFUSE (NoCoverage), never emit a trace that mismatches the
/// oracle. Pins the exact vectors the gate flagged.
#[test]
fn engine_divergent_from_eval_corners_refuse() {
    let cases: &[&str] = &[
        // Direct eval with a spread argument.
        "var it = {}; it[Symbol.iterator] = function(){ var i=0; return { next(){ return i<1?{done:false,value:'0'}:{done:true}; } }; }; \
         (function(){ eval(...it); })();",
        // %TypedArray%.from iterable path with an object element whose ToNumber
        // mutates the source (collect-first vs V8 lazy-read).
        "var values = [0, { valueOf() { values.length = 0; return 100; } }, 2]; Int32Array.from(values);",
        // %TypedArray%.from iterable path with a mapFn.
        "Int16Array.from([1,2,3], function(x){ return x * 10; });",
        "Int8Array.from(new Set([1,2,3]), x => x + 1);",
    ];
    for src in cases {
        match evaluate_case_opts(&[], src, false) {
            SemOutcome::NoCoverage { .. } => {}
            SemOutcome::Trace(t) => {
                panic!("engine-divergent corner unexpectedly produced a trace: {src}\n{t:?}");
            }
        }
    }
}

/// Deep recursion (the tail-call-optimization corpus tests recurse 100000
/// deep) must hit the sem's call-depth cap and become a SOUND Fatal
/// (NoCoverage) — never a stack overflow. On a generous stack (matching the
/// real toolchain's main thread) the 512-deep cap trips cleanly; cargo's 2MB
/// test threads are the artificial constraint, so the corpus sweeps run their
/// bodies on a large-stack thread (see `run_on_big_stack`).
#[test]
fn deep_recursion_caps_not_overflow() {
    run_on_big_stack(|| {
        let sta = "function Test262Error(){} function assert(){} assert.sameValue=function(){};";
        let body = "var callCount = 0;\n\
             (function f(n) { if (n === 0) { callCount += 1; return; } \
             function getF() { return f; } return getF()(n - 1); }(100000));";
        match evaluate_case_opts(&[sta], body, false) {
            SemOutcome::NoCoverage { reason } => {
                assert!(
                    reason.contains("call depth"),
                    "expected a call-depth cap refusal, got: {reason}"
                );
            }
            SemOutcome::Trace(_) => panic!("expected NoCoverage (call-depth cap), got a trace"),
        }
    });
}

/// Run `f` on a thread with a large stack (256 MiB), so the sem's bounded
/// recursion (call-depth cap 512) is reached cleanly instead of overflowing a
/// small test-harness thread stack.
fn run_on_big_stack<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(f)
        .expect("spawn big-stack thread")
        .join()
        .expect("big-stack thread panicked");
}

/// Sem-only totality scan over the feature dirs: no Node, just evaluate every
/// case and confirm none overflows the stack / panics. Prints each file first
/// (flushed) so a fatal abort names the culprit as the last line. Gated behind
/// TRUST_JS_SCAN so it does not slow the normal suite.
#[test]
fn sem_only_totality_scan() {
    if std::env::var("TRUST_JS_SCAN").is_err() {
        eprintln!("SKIP sem_only_totality_scan: set TRUST_JS_SCAN=1");
        return;
    }
    run_on_big_stack(sem_only_totality_scan_body);
}

fn sem_only_totality_scan_body() {
    let corpus = corpus_root();
    let mut include_cache: BTreeMap<String, String> = BTreeMap::new();
    for (dir, cap) in SWEEP_DIRS {
        for path in collect_js_files(&corpus.join(dir), *cap) {
            let Ok(body) = std::fs::read_to_string(&path) else { continue };
            let fm = parse_frontmatter(&body);
            if fm.flags.iter().any(|f| f == "module") {
                continue;
            }
            let raw = fm.flags.iter().any(|f| f == "raw");
            let mut include_names: Vec<String> = if raw {
                Vec::new()
            } else {
                vec!["assert.js".to_string(), "sta.js".to_string()]
            };
            include_names.extend(fm.includes.iter().cloned());
            let mut include_srcs: Vec<String> = Vec::new();
            let mut missing = false;
            for name in &include_names {
                let p = corpus.join("harness").join(name);
                if !p.is_file() {
                    missing = true;
                    break;
                }
                let src = include_cache
                    .entry(name.clone())
                    .or_insert_with(|| std::fs::read_to_string(&p).expect("read include"));
                include_srcs.push(src.clone());
            }
            if missing {
                continue;
            }
            let rel = path.strip_prefix(&corpus).unwrap_or(&path).display().to_string();
            let inc_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();
            for &strict in &[false, true] {
                let sem_body =
                    if strict { format!("\"use strict\";\n{body}") } else { body.clone() };
                eprintln!("SCAN {rel} [{}]", mode_str(strict));
                let _ = std::io::stderr().flush();
                let _ = evaluate_case_opts(&inc_refs, &sem_body, false);
            }
        }
    }
    eprintln!("SCAN COMPLETE");
}

#[test]
fn adversarial_minis_vs_node() {
    let Some(node) = node_bin() else {
        eprintln!("SKIP adversarial_minis_vs_node: set TRUST_JS_NODE");
        return;
    };
    let driver = driver_path();
    assert!(driver.is_file(), "driver not found at {}", driver.display());
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();

    for (tag, body) in MINIS {
        let sem = match catch_unwind(AssertUnwindSafe(|| evaluate_case_opts(&[], body, false))) {
            Ok(o) => o,
            Err(_) => {
                failures.push(format!("{tag}: PANIC in sem"));
                continue;
            }
        };
        let sem_trace = match sem {
            SemOutcome::Trace(t) => t,
            SemOutcome::NoCoverage { reason } => {
                failures.push(format!("{tag}: unexpected NoCoverage: {reason}"));
                continue;
            }
        };
        let nt = node_trace(&node, &driver, tmp.path(), tag, body);
        if !traces_equal(&sem_trace, &nt) {
            failures.push(format!(
                "{tag}: WRONG TRACE: {}",
                explain_divergence(&sem_trace, &nt).unwrap_or_else(|| "unlocalized".to_string())
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "adversarial mini failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// --- corpus sweep -------------------------------------------------------

struct Frontmatter {
    includes: Vec<String>,
    flags: Vec<String>,
    negative: bool,
}

fn parse_frontmatter(body: &str) -> Frontmatter {
    let fm = body
        .split_once("/*---")
        .and_then(|(_, rest)| rest.split_once("---*/"))
        .map_or("", |(fm, _)| fm);
    let mut includes = Vec::new();
    let mut flags = Vec::new();
    let negative = fm.contains("negative:");
    let mut lines = fm.lines().peekable();
    while let Some(line) = lines.next() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("includes:") {
            let rest = rest.trim();
            if let Some(inner) = rest.strip_prefix('[') {
                let inner = inner.trim_end_matches(']');
                includes.extend(
                    inner.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()),
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
                    inner.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()),
                );
            }
        }
    }
    Frontmatter { includes, flags, negative }
}

fn collect_js_files(dir: &Path, cap: usize) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&d) else { continue };
        let mut entries: Vec<PathBuf> = rd.filter_map(|e| e.ok().map(|e| e.path())).collect();
        entries.sort();
        for p in entries {
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|e| e == "js")
                && !p.file_name().is_some_and(|n| n.to_string_lossy().ends_with("_FIXTURE.js"))
            {
                files.push(p);
            }
        }
    }
    files.sort();
    files.truncate(cap);
    files
}

fn short_reason(r: &str) -> String {
    let r = r.split(" (out of slice)").next().unwrap_or(r);
    let r = r.split(':').next().unwrap_or(r);
    r.chars().take(80).collect()
}

/// Directories where async methods, array/call spread, and Array/TypedArray
/// from/of concentrate — swept at full depth (async-generator method dirs are
/// included to confirm they SOUNDLY refuse, never a wrong trace).
const SWEEP_DIRS: &[(&str, usize)] = &[
    // async methods (+ async-gen methods, which must refuse)
    ("test/language/statements/class/async-method", 4000),
    ("test/language/statements/class/async-method-static", 4000),
    ("test/language/statements/class/async-gen-method", 4000),
    ("test/language/statements/class/async-gen-method-static", 4000),
    ("test/language/expressions/class/async-method", 4000),
    ("test/language/expressions/class/async-method-static", 4000),
    ("test/language/expressions/class/async-gen-method", 4000),
    ("test/language/expressions/class/async-gen-method-static", 4000),
    ("test/language/expressions/class/elements", 6000),
    ("test/language/expressions/object", 4000),
    // array-literal / call / new spread
    ("test/language/expressions/array", 2000),
    ("test/language/expressions/call", 2000),
    ("test/language/expressions/new", 2000),
    ("test/language/expressions/spread", 2000),
    // Array.from / Array.of / %TypedArray%.from|of
    ("test/built-ins/Array/from", 2000),
    ("test/built-ins/Array/of", 400),
    ("test/built-ins/TypedArray/from", 2000),
    ("test/built-ins/TypedArray/of", 400),
    ("test/built-ins/TypedArrayConstructors/from", 2000),
    ("test/built-ins/TypedArrayConstructors/of", 400),
];

#[test]
fn corpus_sweep_vs_node() {
    // Deep-recursion corpus cases (TCO tests) reach the sem's 512-deep call cap;
    // a 2MB cargo test thread would overflow before the cap, so run on a large
    // stack matching the real toolchain's main thread.
    run_on_big_stack(corpus_sweep_body);
}

#[allow(clippy::too_many_lines)]
fn corpus_sweep_body() {
    let Some(node) = node_bin() else {
        eprintln!("SKIP corpus_sweep_vs_node: set TRUST_JS_NODE (and optionally TRUST_JS262_CORPUS)");
        return;
    };
    let corpus = corpus_root();
    assert!(
        corpus.join("harness/assert.js").is_file(),
        "corpus harness not found under {}",
        corpus.display()
    );
    let driver = driver_path();
    assert!(driver.is_file(), "driver not found at {}", driver.display());

    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();
    let mut covered = 0u64;
    let mut refused = 0u64;
    let mut equal = 0u64;
    let mut panics = 0u64;
    let mut per_dir: BTreeMap<&str, (u64, u64)> = BTreeMap::new();
    let mut include_cache: BTreeMap<String, String> = BTreeMap::new();
    let mut refusal_reasons: BTreeMap<String, u64> = BTreeMap::new();

    let mut case_no = 0usize;
    for (dir, cap) in SWEEP_DIRS {
        for path in collect_js_files(&corpus.join(dir), *cap) {
            let Ok(body) = std::fs::read_to_string(&path) else { continue };
            let fm = parse_frontmatter(&body);
            if fm.flags.iter().any(|f| f == "module" || f == "CanBlockIsRequired") {
                continue;
            }
            let raw = fm.flags.iter().any(|f| f == "raw");
            let modes: &[bool] = if fm.flags.iter().any(|f| f == "onlyStrict") {
                &[true]
            } else if raw || fm.flags.iter().any(|f| f == "noStrict") {
                &[false]
            } else {
                &[false, true]
            };
            let mut include_names: Vec<String> = if raw {
                Vec::new()
            } else {
                vec!["assert.js".to_string(), "sta.js".to_string()]
            };
            include_names.extend(fm.includes.iter().cloned());
            if fm.flags.iter().any(|f| f == "async")
                && !include_names.iter().any(|n| n == "doneprintHandle.js")
            {
                include_names.push("doneprintHandle.js".to_string());
            }
            let mut include_srcs: Vec<String> = Vec::new();
            let mut include_paths: Vec<String> = Vec::new();
            let mut missing = false;
            for name in &include_names {
                let p = corpus.join("harness").join(name);
                if !p.is_file() {
                    missing = true;
                    break;
                }
                let src = include_cache
                    .entry(name.clone())
                    .or_insert_with(|| std::fs::read_to_string(&p).expect("read include"));
                include_srcs.push(src.clone());
                include_paths.push(p.display().to_string());
            }
            if missing {
                continue;
            }
            let rel = path.strip_prefix(&corpus).unwrap_or(&path).display().to_string();

            for &strict in modes {
                case_no += 1;
                let sem_body =
                    if strict { format!("\"use strict\";\n{body}") } else { body.clone() };
                let inc_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();
                let sem = match catch_unwind(AssertUnwindSafe(|| {
                    evaluate_case_opts(&inc_refs, &sem_body, false)
                })) {
                    Ok(o) => o,
                    Err(_) => {
                        panics += 1;
                        failures.push(format!("{rel} [{}]: PANIC in sem", mode_str(strict)));
                        continue;
                    }
                };
                let sem_trace = match sem {
                    SemOutcome::Trace(t) => t,
                    SemOutcome::NoCoverage { reason } => {
                        refused += 1;
                        per_dir.entry(dir).or_default().1 += 1;
                        *refusal_reasons.entry(short_reason(&reason)).or_insert(0) += 1;
                        continue;
                    }
                };
                covered += 1;
                per_dir.entry(dir).or_default().0 += 1;
                let _ = fm.negative;

                let mode = mode_str(strict);
                let body_path = tmp.path().join(format!("c-{case_no}.body.js"));
                std::fs::write(&body_path, &body).expect("write body");
                let manifest = serde_json::json!({
                    "completion_witness": false,
                    "includes": include_paths,
                    "source": body_path.display().to_string(),
                    "mode": mode,
                    "kind": "script",
                });
                let manifest_path = tmp.path().join(format!("c-{case_no}.manifest.json"));
                let mut mf = std::fs::File::create(&manifest_path).expect("create manifest");
                mf.write_all(manifest.to_string().as_bytes()).expect("write manifest");
                drop(mf);

                let out = Command::new(&node)
                    .arg(&driver)
                    .arg(&manifest_path)
                    .env("TZ", "UTC")
                    .env("LANG", "C")
                    .env("LC_ALL", "C")
                    .output()
                    .expect("spawn node driver");
                let nt = match extract_trace(&out.stdout) {
                    Ok(t) => t,
                    Err(e) => {
                        failures.push(format!(
                            "{rel} [{mode}]: node trace extraction failed: {e} (stderr: {})",
                            String::from_utf8_lossy(&out.stderr)
                        ));
                        continue;
                    }
                };
                if traces_equal(&sem_trace, &nt) {
                    equal += 1;
                } else {
                    failures.push(format!(
                        "{rel} [{mode}]: WRONG TRACE: {}",
                        explain_divergence(&sem_trace, &nt)
                            .unwrap_or_else(|| "unlocalized".to_string())
                    ));
                }
            }
        }
    }

    eprintln!("=== async-method / spread / Array.from-of corpus sweep ===");
    eprintln!("covered={covered} equal={equal} refused={refused} panics={panics}");
    for (dir, (cov, refu)) in &per_dir {
        eprintln!("  {dir}: covered={cov} refused={refu}");
    }
    eprintln!("--- top refusal reasons ---");
    let mut reasons: Vec<_> = refusal_reasons.iter().collect();
    reasons.sort_by(|a, b| b.1.cmp(a.1));
    for (reason, n) in reasons.iter().take(30) {
        eprintln!("  {n:>5}  {reason}");
    }
    assert!(
        failures.is_empty(),
        "corpus sweep failures ({}):\n{}",
        failures.len(),
        failures.iter().take(80).cloned().collect::<Vec<_>>().join("\n")
    );
}

fn mode_str(strict: bool) -> &'static str {
    if strict {
        "strict"
    } else {
        "bare"
    }
}
