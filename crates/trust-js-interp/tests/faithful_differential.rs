// Env-gated differential acceptance for the tier-0 faithful interpreter:
// (a) embedded mini-cases run through BOTH trust_js_interp::evaluate_case and
// the real trace driver on Node, requiring byte-for-byte trace equality;
// (b) a corpus sample — every S0-eligible file (slice-rule filtered) under
// four test262 directories, bytewise-sorted, first 400 — where every run must
// be traces_equal OR a sound NoCoverage refusal: ZERO wrong traces.
// Skips (loudly) when TRUST_JS_NODE is unset.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use trust_js_interp::{evaluate_case, InterpOutcome};
use trust_js_trace::{explain_divergence, extract_trace, traces_equal, ObservableTrace};

/// Where `scripts/js262/fetch_corpus.sh` unpacks the pinned corpus, relative to
/// this crate — a checkout, not a particular developer's home directory.
const DEFAULT_CORPUS: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../build/js262/test262-9e61c12835c5e4a3bdba93850427e6742c4f64c4"
);

/// (dir, per-dir case cap). The four S1a language dirs keep their original
/// combined coverage; the S1b built-ins dirs are capped to keep the runtime
/// sane while sampling the object/array/property machinery densely.
/// `TRUST_JS262_SAMPLE_CAP` overrides every cap and
/// `TRUST_JS262_SAMPLE_SKIP` skips that many eligible cases per dir first
/// (for wider adversarial sweeps beyond the committed sample).
const SAMPLE_DIRS: [(&str, usize); 73] = [
    // §26 WeakRef / FinalizationRegistry + §27.1 the abstract %Iterator%
    // constructor and %Iterator.prototype% (constructor / @@toStringTag
    // accessors + @@iterator). The iterator-helper methods (map/filter/take/...)
    // and the static sequencing helpers (from/concat/zip) are proposal surface
    // both engines ship but this slice does not model: they refuse (NoCoverage).
    ("test/built-ins/WeakRef", 40),
    ("test/built-ins/FinalizationRegistry", 60),
    ("test/built-ins/Iterator", 600),
    // for-in over intrinsic-namespace objects (Math/JSON/Reflect/...): empty
    // enumerable surface, exact vs both engines.
    ("test/language/statements/for-in", 200),
    // M2 D1: Promise + async/await onto the deterministic reactor. Promise
    // object model, then/catch/finally, resolve/reject/all/allSettled/race/any,
    // thenable assimilation, queueMicrotask + setTimeout; async functions /
    // arrows desugared onto the reactor (await reuses the generator resumption
    // machine). Async generators / for-await / top-level await refuse soundly.
    ("test/built-ins/Promise", 160),
    ("test/built-ins/AsyncFunction", 60),
    ("test/language/statements/async-function", 120),
    ("test/language/expressions/async-function", 120),
    ("test/language/expressions/async-arrow-function", 120),
    ("test/language/expressions/await", 120),
    // S1f: sloppy-mode semantics + eval + the Function constructor. Direct eval
    // (PerformEval in the caller context, var/function hoisting into the
    // caller's variable environment), indirect eval (global scope), and
    // CreateDynamicFunction; `with` refuses soundly (out of slice).
    ("test/language/eval-code/direct", 250),
    ("test/language/eval-code/indirect", 120),
    ("test/built-ins/eval", 20),
    ("test/built-ins/Function", 320),
    ("test/language/statements/with", 120),
    ("test/language/arguments-object", 200),
    ("test/language/expressions/addition", 200),
    ("test/language/statements/if", 200),
    ("test/language/statements/while", 200),
    ("test/built-ins/Object", 200),
    ("test/built-ins/Array", 200),
    ("test/built-ins/Symbol", 200),
    ("test/built-ins/AggregateError", 200),
    ("test/built-ins/String", 200),
    ("test/built-ins/Reflect", 200),
    ("test/language/statements/class", 200),
    ("test/language/expressions/class", 200),
    // S1e: private class elements (instance + static fields/methods/
    // accessors, brand checks) and the user iterator protocol (for-of over
    // arbitrary iterables with IteratorClose).
    ("test/language/statements/class/elements", 220),
    ("test/language/expressions/class/elements", 120),
    ("test/language/statements/for-of", 180),
    // S1e: generators — the resumption state machine over blocks, if,
    // while/do/for, for-of, try/catch/finally, labels; yield / yield*
    // delegation; next/return/throw resumption; the generator prototype graph.
    ("test/language/statements/generators", 180),
    ("test/language/expressions/generators", 180),
    ("test/built-ins/GeneratorFunction", 100),
    ("test/built-ins/GeneratorPrototype", 100),
    // S1c: standard-library core (Map/Set/Weak*/Date/JSON/RegExp skeleton/
    // URI). Caps keep the wall clock sane; the pre-landing sweep ran these
    // dirs uncapped.
    ("test/built-ins/Map", 200),
    ("test/built-ins/Set", 150),
    ("test/built-ins/WeakMap", 100),
    ("test/built-ins/WeakSet", 100),
    ("test/built-ins/Date", 250),
    ("test/built-ins/JSON", 200),
    ("test/built-ins/RegExp", 150),
    // §10.5 Proxy is fully live (13 traps + invariants, constructor,
    // Proxy.revocable); the whole dir was swept uncapped at zero-wrong.
    ("test/built-ins/Proxy", 250),
    ("test/built-ins/decodeURIComponent", 60),
    ("test/built-ins/encodeURIComponent", 60),
    // Binary data (§25 ArrayBuffer/DataView, §23.2 %TypedArray% + concrete
    // constructors + the integer-indexed exotic). The pre-landing sweep ran
    // these dirs at cap 250 (1465 covered runs, zero wrong); caps here keep the
    // committed wall clock sane while sampling the surface densely.
    ("test/built-ins/ArrayBuffer", 150),
    ("test/built-ins/DataView", 150),
    ("test/built-ins/TypedArray", 200),
    ("test/built-ins/TypedArrayConstructors", 150),
    ("test/built-ins/Uint8Array", 70),
    // BigInt: the arbitrary-precision value type — literals (all bases),
    // BigInt::* arithmetic/bitwise/shift with the mixed-type TypeError rule,
    // the BigInt() function + NumberToBigInt integrality, prototype
    // toString(radix)/valueOf, asIntN/asUintN wrap, and the ToBigInt
    // coercions. The BigInt-typed arrays (BigInt64Array/BigUint64Array) read
    // and write their elements as BigInt; the DataView getBig*/setBig* lanes
    // round-trip the signed/unsigned 64-bit wrap. Pre-landing these dirs ran
    // uncapped (zero wrong across BigInt + typed-array + DataView + operator
    // dirs); caps here keep the committed wall clock sane.
    ("test/built-ins/BigInt", 200),
    ("test/language/literals/bigint", 100),
    ("test/built-ins/TypedArrayConstructors/BigInt64Array", 60),
    ("test/built-ins/TypedArrayConstructors/BigUint64Array", 60),
    ("test/built-ins/TypedArrayConstructors/ctors-bigint", 120),
    ("test/built-ins/DataView/prototype/getBigInt64", 60),
    ("test/built-ins/DataView/prototype/setBigInt64", 60),
    ("test/built-ins/DataView/prototype/setBigUint64", 60),
    // S1e: the built-in iterator objects — %ArrayIteratorPrototype% (shared by
    // Array + TypedArray iterators), %StringIteratorPrototype%,
    // %MapIteratorPrototype%, %SetIteratorPrototype% + their %IteratorPrototype%
    // root, and the Array/TypedArray/Map/Set values/keys/entries + @@iterator
    // factories. Each iterator object is a fixed state machine over its live
    // source producing exact {value,done} results; console.log'd it projects as
    // an ordinary `{}` (its @@toStringTag lives on the prototype). The
    // *IteratorPrototype dirs were swept uncapped at zero-wrong; caps keep the
    // committed wall clock sane while sampling densely.
    ("test/built-ins/ArrayIteratorPrototype", 40),
    ("test/built-ins/MapIteratorPrototype", 20),
    ("test/built-ins/SetIteratorPrototype", 20),
    ("test/built-ins/StringIteratorPrototype", 20),
    ("test/built-ins/Array/prototype/values", 20),
    ("test/built-ins/Array/prototype/keys", 20),
    ("test/built-ins/Array/prototype/entries", 20),
    ("test/built-ins/Map/prototype/entries", 20),
    ("test/built-ins/Map/prototype/keys", 20),
    ("test/built-ins/Map/prototype/values", 20),
    ("test/built-ins/Set/prototype/values", 20),
    ("test/built-ins/Set/prototype/entries", 20),
    ("test/built-ins/String/prototype/Symbol.iterator", 20),
    ("test/built-ins/TypedArray/prototype/values", 30),
    ("test/built-ins/TypedArray/prototype/keys", 30),
    ("test/built-ins/TypedArray/prototype/entries", 30),
];

struct Env {
    node: String,
    /// The second engine, when present (either-engine divergence audit).
    bun: Option<String>,
    corpus: PathBuf,
    driver: PathBuf,
    tmp: tempfile::TempDir,
}

fn env_or_skip(test: &str) -> Option<Env> {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!(
            "SKIP {test}: set TRUST_JS_NODE to a node binary (and optionally \
             TRUST_JS262_CORPUS) to run the differential"
        );
        return None;
    };
    let corpus = PathBuf::from(
        std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string()),
    );
    assert!(
        corpus.join("harness/assert.js").is_file(),
        "corpus harness not found under {}",
        corpus.display()
    );
    let driver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs");
    assert!(driver.is_file(), "driver not found at {}", driver.display());
    // Second engine: where Node and the head disagree, the audited Node-vs-Bun
    // divergences (e.g. the upsert methods Node 24 lacks) are resolved by the
    // SAME either-engine rule the four-head calibration applies. Optional — if
    // no bun is resolvable the differential runs Node-only.
    let bun = std::env::var("TRUST_JS_BUN").ok().filter(|v| !v.trim().is_empty()).or_else(bun_on_path);
    Some(Env {
        node,
        bun,
        corpus,
        driver,
        tmp: tempfile::tempdir().expect("tempdir"),
    })
}

/// First executable `bun` along `PATH`.
fn bun_on_path() -> Option<String> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .filter(|dir| !dir.as_os_str().is_empty())
        .map(|dir| dir.join("bun"))
        .find(|cand| cand.is_file())
        .map(|p| p.display().to_string())
}

/// One driver run (completion witness OFF, like the head).
fn node_trace(
    env: &Env,
    tag: &str,
    include_paths: &[PathBuf],
    body: &str,
    strict: bool,
) -> Result<ObservableTrace, String> {
    engine_trace(env, &env.node.clone(), tag, include_paths, body, strict)
}

fn engine_trace(
    env: &Env,
    engine: &str,
    tag: &str,
    include_paths: &[PathBuf],
    body: &str,
    strict: bool,
) -> Result<ObservableTrace, String> {
    let body_path = env.tmp.path().join(format!("{tag}.body.js"));
    std::fs::write(&body_path, body).expect("write body");
    let includes_json: Vec<String> = include_paths
        .iter()
        .map(|p| p.display().to_string())
        .collect();
    let manifest = serde_json::json!({
        "includes": includes_json,
        "source": body_path.display().to_string(),
        "mode": if strict { "strict" } else { "bare" },
        "kind": "script",
    });
    let manifest_path = env.tmp.path().join(format!("{tag}.manifest.json"));
    let mut mf = std::fs::File::create(&manifest_path).expect("create manifest");
    mf.write_all(manifest.to_string().as_bytes())
        .expect("write manifest");
    drop(mf);
    let out = Command::new(engine)
        .arg(&env.driver)
        .arg(&manifest_path)
        .env("TZ", "UTC")
        .env("LANG", "C")
        .env("LC_ALL", "C")
        .output()
        .expect("spawn node driver");
    extract_trace(&out.stdout).map_err(|e| {
        format!(
            "trace extraction failed: {e} (stderr: {})",
            String::from_utf8_lossy(&out.stderr)
        )
    })
}

// ---------------------------------------------------------------------------
// (a) Embedded mini-cases: must be COVERED and trace-equal.
// ---------------------------------------------------------------------------

struct Mini {
    name: &'static str,
    with_harness: bool,
    strict: bool,
    body: &'static str,
}

#[allow(clippy::too_many_lines)]
fn mini_cases() -> Vec<Mini> {
    let m = |name, with_harness, strict, body| Mini {
        name,
        with_harness,
        strict,
        body,
    };
    vec![
        m("number-repr", false, false,
          "console.log(1 + 2, 0.1 + 0.2, 1e21, 1e-7, 5e-324, 123456789, 100, 0.000001, 1.7976931348623157e308);"),
        m("negative-zero-nan", false, false,
          "console.log(-0, NaN, Infinity, -Infinity, String(-0), 0);"),
        m("coercion", false, false,
          "console.log('a' + 1, '5' * '2', +true, -'3', 1 + null, 1 + undefined, 'x' + undefined, '' + {}, Number('0x10'), Number(''), Boolean(''), isNaN('abc'));"),
        m("comparison-logic", false, false,
          "console.log(1 < 2, '10' < '9', 2 <= 2, null == undefined, null === undefined, NaN == NaN, 1 == '1', 0 == false, typeof 5, typeof undefined, typeof null, typeof console.log, true && 0, false || 'x', !1, 1 ? 'a' : 'b');"),
        m("bitwise-shift", false, false,
          "console.log(5 & 3, 5 | 3, 5 ^ 3, ~5, 1 << 31, -1 >>> 0, -8 >> 1, 2 ** 10, (-2) ** 3, 7 % 3, -7 % 3);"),
        m("loops", false, false,
          "var s = 0; for (var i = 0; i < 10; i++) { s += i; } var j = 0; while (j < 3) j++; do j--; while (j > 1); console.log(s, i, j);"),
        m("labels", false, false,
          "var out = []; outer: for (var a = 0; a < 3; a++) { for (var b = 0; b < 3; b++) { if (b === 1) continue outer; if (a === 2) break outer; out.push(a * 10 + b); } } console.log(out);"),
        m("for-in-order", false, false,
          "var o = { b: 1, 2: 'two', a: 3, 0: 'zero' }; var ks = []; for (var k in o) ks.push(k); console.log(ks);"),
        m("for-of-array-string", false, false,
          "var acc = []; for (var v of [10, 20]) acc.push(v); for (var ch of 'ab') acc.push(ch); console.log(acc);"),
        m("functions-closures", false, false,
          "function mk(n) { return function (m) { return n + m; }; } var f = mk(40); console.log(f(2), mk(1)(1), typeof mk, mk.length, f.name);"),
        m("arrow-lexical-this", false, false,
          "var o = { v: 40, m: function () { var g = () => this.v + 2; return g(); } }; console.log(o.m(), (() => 7)());"),
        m("default-rest-params", false, false,
          "function f(a, b = a + 1, ...r) { return [a, b, r]; } console.log(f(1), f(1, 2, 3, 4), f.length);"),
        m("arguments-mapped", false, false,
          "function f(a, b) { a = 42; var x = arguments[0]; arguments[1] = 7; var y = b; delete arguments[0]; a = 9; console.log(x, y, arguments[0], arguments.length, arguments.callee === f); } f(1, 2);"),
        m("arguments-dup-params", false, false,
          "function d(x, x) { x = 99; console.log(arguments[0], arguments[1]); } d(1, 2);"),
        m("arguments-strict-unmapped", false, false,
          "function s(a) { 'use strict'; a = 5; var t = false; try { arguments.callee; } catch (e) { t = e instanceof TypeError; } console.log(arguments[0], t); } s(1);"),
        m("arguments-projection", false, false,
          "function f(a) { console.log(arguments); } f(1, 'two');"),
        m("try-catch-finally", false, false,
          "var r = []; try { r.push('t'); throw 7; } catch (e) { r.push(e); } finally { r.push('f'); } console.log(r);"),
        m("switch-fallthrough", false, false,
          "var fall = []; switch (2) { case 1: fall.push(1); case 2: fall.push(2); case 3: fall.push(3); break; case 4: fall.push(4); } console.log(fall);"),
        m("string-basics", false, false,
          "console.log('abc'.length, 'abc'[1], 'a' < 'b', 'abc' + 'def', 'caf\\u00e9', 'tab\\ttext', 'q\\\"b\\\\s', 'hello'.charAt(1), 'hello'.charCodeAt(0), 'hello'.indexOf('ll'));"),
        m("template-literals", false, false,
          "var x = 6; console.log(`a${x * 7}b`, `${'q'}${x}`, `multi\nline`.length);"),
        m("object-array-projection", false, false,
          "var o = { b: 1, 2: 'two', a: [1, 2, ['deep']], n: null }; o.self = o; console.log(o, [7, 8], {});"),
        m("accessor-projection", false, false,
          "var n = 0; var o = { get x() { n++; return 1; }, set y(v) {} }; console.log(o, n);"),
        m("thrown-native-error", false, false, "throw new RangeError('r');"),
        m("thrown-primitive", false, false, "throw 42;"),
        m("constructor-identity", false, false,
          "function A() {} var a = new A(); console.log(a instanceof A, a.constructor === A, typeof A.prototype, a instanceof Object);"),
        m("new-target", false, false,
          "function C() { console.log(new.target === C); } new C(); C();"),
        m("destructuring", false, false,
          "var [a, , b = 10, ...r] = [1, 2, undefined, 4, 5]; var { x, y: z = 3, ...rest } = { x: 1, w: 9 }; console.log(a, b, r, x, z, rest);"),
        m("spread", false, false,
          "function f(a, b, c) { return a + b + c; } console.log(f(...[1, 2, 3]), [0, ...[1, 2], 3], { ...{ a: 1 }, b: 2 });"),
        m("optional-chaining", false, false,
          "var o = { a: { b: 1 }, f: function () { return 2; } }; var n = null; console.log(o?.a?.b, n?.a?.b, n?.f(), o.f?.(), o.missing?.());"),
        m("refkey-double-coercion", false, false,
          "var n = 0; var o = {}; var p = { toString: function () { n++; return 'k'; } }; o[p] += 1; var q = { toString: function () { return 'j'; } }; o[q] = 1; console.log(n, o.k, o.j);"),
        m("member-null-late-typeerror", false, false,
          "var order = []; function k() { order.push('k'); return 'p'; } var base = null; var t1 = false; try { base[k()] = order.push('rhs'); } catch (e) { t1 = e instanceof TypeError; } console.log(t1, order);"),
        m("defineproperty-descriptors", false, false,
          "var o = {}; Object.defineProperty(o, 'x', { value: 1, writable: false, enumerable: false, configurable: true }); var d = Object.getOwnPropertyDescriptor(o, 'x'); console.log(d, o.x, delete o.x, o.x, Object.keys({ b: 1, 0: 'z', a: 2 }));"),
        m("call-apply-bind", false, false,
          "function add(a, b) { return this.base + a + b; } var bound = add.bind({ base: 100 }, 1); console.log(bound(2), bound.name, bound.length, add.apply({ base: 10 }, [1, 2]), add.call({ base: 20 }, 1, 2));"),
        m("wrappers", false, false,
          "var w = new String('ab'); console.log(typeof w, w.length, w[0], w.valueOf(), (new Number(5)).valueOf(), (new Boolean(false)).valueOf(), Object.prototype.toString.call(5));"),
        m("array-exotics", false, false,
          "var a = [1, 2, 3]; a.length = 1; a[5] = 9; var t = false; try { a.length = -1; } catch (e) { t = e instanceof RangeError; } console.log(a, t, [1, 2].concat([3], 4), [1, 2, 3].slice(1), [5, 6, 5].indexOf(5, 1));"),
        m("array-inherited-elements", false, false,
          "Array.prototype[1] = 9; var x = [0]; x.length = 2; var s = x.slice(); console.log(s.hasOwnProperty('1'), s[1], x.indexOf(9), x.pop(), x.length);"),
        m("per-iteration-let", false, false,
          "var fns = []; for (let i = 0; i < 3; i++) { fns.push(function () { return i; }); } console.log(fns[0](), fns[1](), fns[2]());"),
        m("tdz-closure", false, false,
          "function f() { x = 1; } var t = false; try { f(); } catch (e) { t = e instanceof ReferenceError; } let x; f(); console.log(t, x);"),
        m("strict-mode-body", false, true, "var y = 21; console.log(y * 2, typeof this);"),
        m("strict-nonwritable-fn-length", false, true,
          "function f(a, b) {} var t = false; try { f.length = 5; } catch (e) { t = e instanceof TypeError; } console.log(t, f.length, f.name);"),
        m("harness-assert-pass", true, false,
          "assert.sameValue(1 + 1, 2, 'arith'); assert.notSameValue(-0, 0); assert(true); console.log('ok');"),
        m("harness-test262error-throw", true, false, "assert.sameValue(1, 2, 'boom');"),
        m("harness-assert-throws", true, false,
          "assert.throws(TypeError, function () { null.x; }); assert.throws(Test262Error, function () { throw new Test262Error('x'); }); console.log('done');"),
        m("harness-compare-array", true, false,
          "assert.compareArray([1, -0, NaN], [1, -0, NaN]); var t = false; try { assert.compareArray([1], [2]); } catch (e) { t = e.constructor === Test262Error; } console.log(t);"),
        m("harness-donotevaluate", true, false, "$DONOTEVALUATE();"),
        m("console-fn-surface", false, false,
          "console.log(console.log.name, console.log.length, typeof console.log, print.name, print.length);"),
        m("error-tostring", false, false,
          "console.log(new TypeError('x').toString(), String(new RangeError('')), '' + new Error('e'));"),
        // ---- S1b: Object statics --------------------------------------
        m("object-assign", false, false,
          "var log = []; var src = { a: 1, get b() { log.push('g'); return 2; } };\n\
           var t = Object.assign({ a: 0 }, src, null, 'xy', { c: 3 });\n\
           console.log(t, log, Object.assign(t) === t, t[0], t[1]);"),
        m("object-entries-values", false, false,
          "var o = { b: 1, 0: 'z', a: 2 }; console.log(Object.entries(o), Object.values(o), Object.entries('ab'));"),
        m("object-entries-getter-delete", false, false,
          "var o = { get a() { delete o.b; return 1; }, b: 2 };\n\
           console.log(Object.entries(o), Object.values(o));"),
        m("object-fromentries", false, false,
          "var o = Object.fromEntries([['a', 1], ['b', 2], ['a', 3]]);\n\
           var t = false; try { Object.fromEntries([1]); } catch (e) { t = e instanceof TypeError; }\n\
           console.log(o, t);"),
        m("object-descriptors", false, false,
          "var d = Object.getOwnPropertyDescriptors({ a: 1, get g() { return 2; } });\n\
           console.log(d, Object.getOwnPropertyDescriptor([1], 'length'));"),
        m("object-defineproperties-create", false, false,
          "var o = Object.defineProperties({}, { x: { value: 7 }, y: { value: 8, enumerable: true } });\n\
           var c = Object.create(null, { z: { value: 9, enumerable: true } });\n\
           console.log(o.x, o.y, Object.keys(o), c.z, Object.getPrototypeOf(c));"),
        m("object-freeze-seal", false, false,
          "var o = Object.freeze({ a: 1 }); o.a = 2; o.b = 3;\n\
           var s = Object.seal({ x: 1 }); s.x = 5; delete s.x; s.y = 6;\n\
           var a = Object.freeze([1, 2]);\n\
           var t = false; try { 'use strict'; (function () { 'use strict'; a[0] = 9; })(); } catch (e) { t = e instanceof TypeError; }\n\
           console.log(o, s, a, t, Object.isFrozen(o), Object.isSealed(s), Object.isFrozen(s),\n\
           Object.isFrozen(1), Object.isFrozen({}), Object.freeze(5));"),
        m("object-setprototypeof-hasown", false, false,
          "var p = { m() { return 1; } }; var o = {};\n\
           Object.setPrototypeOf(o, p);\n\
           var t = false; try { Object.setPrototypeOf(p, o); } catch (e) { t = e instanceof TypeError; }\n\
           var t2 = false; try { Object.setPrototypeOf(Object.prototype, { }); } catch (e) { t2 = e instanceof TypeError; }\n\
           console.log(o.m(), t, t2, Object.setPrototypeOf(5, null), Object.hasOwn(o, 'm'), Object.hasOwn(p, 'm'));"),
        m("object-freeze-arguments", false, false,
          "function f(a, b) { Object.freeze(arguments); a = 9; arguments[1] = 8;\n\
           console.log(arguments[0], arguments[1], b, Object.isFrozen(arguments)); } f(1, 2);"),
        // ---- S1b: Array methods ---------------------------------------
        m("array-at-includes-lastindexof", false, false,
          "var a = [1, NaN, 3]; console.log(a.at(-1), a.at(0), a.at(9), a.includes(NaN),\n\
           [1, , 3].includes(undefined), a.lastIndexOf(3), [2, 2, 2].lastIndexOf(2, -2), [].lastIndexOf(1));"),
        m("array-iteration-callbacks", false, false,
          "var a = [1, 2, 3, 4];\n\
           console.log(a.every(function (x) { return x > 0; }), a.some(function (x) { return x > 3; }),\n\
           a.filter(function (x, i, arr) { return x % 2 === 0 && arr === a; }),\n\
           a.find(function (x) { return x > 2; }), a.findIndex(function (x) { return x > 2; }),\n\
           a.findLast(function (x) { return x < 4; }), a.findLastIndex(function (x) { return x < 4; }),\n\
           [, 1].find(function (x) { return x === undefined; }) === undefined);"),
        m("array-flat-flatmap", false, false,
          "console.log([1, [2, [3, [4]]]].flat(), [1, [2, [3]]].flat(Infinity), [[1], , [2]].flat(),\n\
           [1, 2].flatMap(function (x) { return [x, [x]]; }));"),
        m("array-reduce", false, false,
          "var t = false; try { [].reduce(function () {}); } catch (e) { t = e instanceof TypeError; }\n\
           console.log([1, 2, 3].reduce(function (a, b) { return a + b; }),\n\
           [1, 2, 3].reduce(function (a, b) { return a + b; }, 10),\n\
           [1, 2, 3].reduceRight(function (a, b) { return a - b; }),\n\
           [, 5, , 6].reduce(function (a, b) { return a + b; }), t);"),
        m("array-mutators", false, false,
          "var a = [1, 2, 3]; a.reverse();\n\
           var f = [0, 0, 0, 0]; f.fill(7, 1, 3); f.fill(8, -1);\n\
           var c = [1, 2, 3, 4, 5]; c.copyWithin(0, 3); c.copyWithin(1, 0, 2);\n\
           var s = [1, 2, 3]; var sh = s.shift(); var un = s.unshift(9, 8);\n\
           console.log(a, f, c, s, sh, un);"),
        m("array-reverse-holes", false, false,
          "var a = [1, , 3]; a.reverse(); console.log(a, a.hasOwnProperty('1'), 0 in a, 2 in a);"),
        m("array-splice", false, false,
          "var a = [1, 2, 3, 4, 5]; var r = a.splice(1, 2, 'x');\n\
           var b = ['a', 'b']; var r2 = b.splice();\n\
           var c = [1, 2, 3]; var r3 = c.splice(-2);\n\
           console.log(a, r, b, r2, c, r3);"),
        m("array-sort-default", false, false,
          "console.log([3, 1, 10, 2].sort(), ['b', 'a', 'c'].sort(), [1, , undefined, 'x'].sort(),\n\
           [,'b', , 'a'].sort().length, ['b', undefined, 'a'].sort()[2] === undefined,\n\
           [-0, 0, 1].sort(), [true, false, null].sort());"),
        m("array-sort-comparator", false, false,
          "console.log([3, 1, 10, 2].sort(function (a, b) { return a - b; }),\n\
           [3, 1, 10, 2].sort(function (a, b) { return b - a; }),\n\
           ['b', 'a'].sort(function (a, b) { return a < b ? -1 : a > b ? 1 : 0; }),\n\
           [5, 1, 4].sort(function (a, b) { var d = a - b; return d; }),\n\
           [2, 1].sort(function (a, b) { return a - b; }) instanceof Array);"),
        m("array-sort-badcomparator-typeerror", false, false,
          "var t = false; try { [1, 2].sort('x'); } catch (e) { t = e instanceof TypeError; }\n\
           var t2 = false; try { [1, 2].sort(null); } catch (e) { t2 = e instanceof TypeError; }\n\
           console.log(t, t2, [9].sort(function (a, b) { return a - b; }));"),
        m("array-tosorted-toreversed-with-tospliced", false, false,
          "var a = [3, 1, 2];\n\
           console.log(a.toSorted(), a.toReversed(), a.with(1, 'w'), a.toSpliced(1, 1, 'p', 'q'), a,\n\
           [1, , 3].toReversed(), [1, , 3].toSorted());"),
        m("array-from-of", false, false,
          "console.log(Array.from([1, 2]), Array.from('ab'), Array.from({ length: 2, 0: 'x', 1: 'y' }),\n\
           Array.from([1, 2], function (x, i) { return x * 10 + i; }),\n\
           Array.from((function () { return arguments; })(5, 6)),\n\
           Array.of(7, 'a'), Array.of(), Array.from({ length: -1 }).length);"),
        m("array-species-subclass", false, false,
          "class MyArr extends Array {}\n\
           var msg = MyArr.from([1, 2, 3]);\n\
           var sliced = msg.slice(1);\n\
           console.log(msg instanceof MyArr, sliced instanceof MyArr, sliced.length, sliced[0],\n\
           msg.filter(function (x) { return x > 1; }) instanceof MyArr,\n\
           msg.map(function (x) { return x; }) instanceof MyArr, MyArr.of(9)[0]);"),
        m("array-species-null-ctor", false, false,
          "var a = [1, 2]; a.constructor = null;\n\
           var t = false; try { a.slice(); } catch (e) { t = e instanceof TypeError; }\n\
           var b = [1, 2]; b.constructor = undefined;\n\
           console.log(t, b.slice() instanceof Array);"),
        m("array-concat-spreadable", false, false,
          "var o = { length: 2, 0: 'a', 1: 'b' };\n\
           o[Symbol.isConcatSpreadable] = true;\n\
           var no = [1, 2]; no[Symbol.isConcatSpreadable] = false;\n\
           console.log([0].concat(o, no, 3));"),
        // ---- S1b: Symbol ----------------------------------------------
        m("symbol-basics", false, false,
          "var s1 = Symbol('one'); var t = Symbol();\n\
           console.log(typeof s1, s1 === Symbol('one'), s1.description, t.description,\n\
           s1.toString(), String(s1), Symbol.iterator.description, s1);"),
        m("symbol-registry", false, false,
          "console.log(Symbol.for('k') === Symbol.for('k'), Symbol.keyFor(Symbol.for('k')),\n\
           Symbol.keyFor(Symbol('x')), Symbol.for('k') === Symbol('k'), Symbol.for('r'));"),
        m("symbol-keys", false, false,
          "var k = Symbol('key'); var o = { a: 1 };\n\
           o[k] = 42;\n\
           console.log(o[k], o, Object.getOwnPropertySymbols(o).length,\n\
           Object.getOwnPropertySymbols(o)[0] === k, Object.keys(o), k in o,\n\
           JSON.stringify(k) === undefined);"),
        m("symbol-errors", false, false,
          "var t1 = false, t2 = false, t3 = false;\n\
           try { new Symbol(); } catch (e) { t1 = e instanceof TypeError; }\n\
           try { '' + Symbol(); } catch (e) { t2 = e instanceof TypeError; }\n\
           try { Symbol.keyFor('nope'); } catch (e) { t3 = e instanceof TypeError; }\n\
           console.log(t1, t2, t3, Symbol.length, Symbol.name, Symbol.prototype.constructor === Symbol);"),
        m("symbol-wellknown-protocols", false, false,
          "var o = {}; o[Symbol.toPrimitive] = function (hint) { return hint === 'number' ? 42 : 'str'; };\n\
           var tagged = {}; tagged[Symbol.toStringTag] = 'Custom';\n\
           function C() {} Object.defineProperty(C, Symbol.hasInstance, { value: function (v) { return v === 1; } });\n\
           console.log(+o, `${o}`, o + 1, Object.prototype.toString.call(tagged),\n\
           1 instanceof C, 2 instanceof C, Object.prototype.toString.call(Math),\n\
           Object.prototype.toString.call(JSON), Object.prototype.toString.call(Symbol()));"),
        m("symbol-object-wrapper", false, false,
          "var s = Symbol('w'); var w = Object(s);\n\
           console.log(typeof w, w.description, w.toString(), w == s, w === s,\n\
           Object.prototype.toString.call(w), w.valueOf() === s);"),
        // ---- S1b: Error family ----------------------------------------
        m("aggregate-error", false, false,
          "var e = new AggregateError([1, 'two'], 'msg');\n\
           var bare = new AggregateError([]);\n\
           var t = false; try { new AggregateError(); } catch (er) { t = er instanceof TypeError; }\n\
           console.log(e instanceof AggregateError, e instanceof Error, e.errors, e.message,\n\
           e.name, bare.errors.length, 'message' in bare, t, AggregateError.length,\n\
           Object.getOwnPropertyDescriptor(e, 'errors').enumerable, e.toString());"),
        m("error-cause-and-ctor-chain", false, false,
          "var e = new Error('m', { cause: 42 });\n\
           var n = new TypeError('t', { cause: undefined });\n\
           console.log(e.cause, 'cause' in e, 'cause' in n, 'cause' in new Error('x'),\n\
           Object.getPrototypeOf(TypeError) === Error, Object.getPrototypeOf(AggregateError) === Error,\n\
           new RangeError('r', { cause: 'c' }).cause);"),
        // ---- S1b: String methods --------------------------------------
        m("string-search-methods", false, false,
          "var s = 'hello world';\n\
           console.log(s.at(-1), s.at(99), s.codePointAt(0), '\\u{1F600}'.codePointAt(0), '\\u{1F600}'.codePointAt(1),\n\
           s.lastIndexOf('o'), s.lastIndexOf('o', 5), s.includes('world'), s.includes('x'),\n\
           s.startsWith('hello'), s.startsWith('world', 6), s.endsWith('world'), s.endsWith('hello', 5));"),
        m("string-slice-substring-split", false, false,
          "var s = 'hello world';\n\
           console.log(s.slice(-5), s.slice(2, -2), s.substring(4, 1), s.substring(-3, 4),\n\
           s.split(' '), 'a,b,,c'.split(','), 'abc'.split(''), ''.split(','), ''.split(''),\n\
           'aXbXc'.split('X', 2), 'aa'.split('a'));"),
        m("string-case-trim", false, false,
          "console.log('AbC'.toLowerCase(), 'aBc'.toUpperCase(), '\\t x \\n'.trim(),\n\
           ' x '.trimStart(), ' x '.trimEnd(), ' x '.trimLeft(), 'x '.trimRight(),\n\
           String.prototype.trimLeft === String.prototype.trimStart);"),
        m("string-pad-repeat-concat", false, false,
          "var t = false; try { 'a'.repeat(-1); } catch (e) { t = e instanceof RangeError; }\n\
           console.log('ab'.repeat(3), 'ab'.repeat(0), t, '5'.padStart(3, '0'), 'ab'.padEnd(5, 'cd'),\n\
           'abc'.padStart(2), 'x'.padStart(4), 'a'.concat('b', 1, null));"),
        m("string-replace", false, false,
          "console.log('aXbXc'.replace('X', '-'), 'aXbXc'.replaceAll('X', '-'),\n\
           'abc'.replace('b', '[$&][$`][$\\'][$$]'), 'abc'.replace('q', 'z'),\n\
           'aa'.replaceAll('', '-'), 'abc'.replace('b', function (m, p, s) { return m + p + s.length; }),\n\
           'x'.replace('x', '$1'));"),
        m("string-statics", false, false,
          "console.log(String.fromCharCode(104, 105), String.fromCharCode(0x10061), String.fromCodePoint(128512),\n\
           String.raw`a\\n${1}b`, String.raw({ raw: ['x', 'z'] }, 'y'),\n\
           'ab'.isWellFormed(), 'ab'.toWellFormed());"),
        m("string-wellformed-surrogates", false, false,
          "var lone = 'a\\uD800b';\n\
           console.log(lone.isWellFormed(), lone.toWellFormed(), '\\u{1F600}'.isWellFormed());"),
        // ---- S1b: Number / parse / Math -------------------------------
        m("number-statics", false, false,
          "console.log(Number.isInteger(5), Number.isInteger(5.5), Number.isInteger('5'),\n\
           Number.isNaN(NaN), Number.isNaN('NaN'), Number.isFinite('5'), Number.isFinite(5),\n\
           Number.isSafeInteger(2 ** 53), Number.isSafeInteger(2 ** 53 - 1),\n\
           Number.MAX_SAFE_INTEGER, Number.MIN_SAFE_INTEGER, Number.EPSILON, Number.MAX_VALUE,\n\
           Number.MIN_VALUE, Number.parseInt === parseInt, Number.parseFloat === parseFloat);"),
        m("parseint-parsefloat", false, false,
          "console.log(parseInt('  42px'), parseInt('ff', 16), parseInt('0x1F'), parseInt('-0x10'),\n\
           parseInt('10', 2), parseInt('z', 36), parseInt('08'), parseInt(''), parseInt('42', 1),\n\
           parseInt('-0'), 1 / parseInt('-0'), parseFloat('3.5e1x'), parseFloat('.5.'),\n\
           parseFloat('abc'), parseFloat('  Infinity!'), parseFloat('-1e'),\n\
           parseInt('123456789012345678901234567890'));"),
        m("math-exact-additions", false, false,
          "console.log(Math.round(2.5), Math.round(-2.5), Math.round(0.49999999999999994), Math.round(-0.4),\n\
           1 / Math.round(-0.4), Math.sign(-3), Math.sign(0), Math.sign(-0), Math.sqrt(9), Math.sqrt(2),\n\
           Math.sqrt(-1), Math.imul(3, 4), Math.imul(0xffffffff, 5), Math.clz32(1), Math.clz32(0),\n\
           Math.fround(5.5), Math.fround(0.1));"),
        m("number-tostring-radix", false, false,
          "console.log((255).toString(16), (8).toString(2), (-255).toString(16), (35).toString(36),\n\
           (0).toString(2), (NaN).toString(16), (Infinity).toString(2),\n\
           (9007199254740991).toString(36));"),
        // ---- S1b: classes ---------------------------------------------
        m("class-base", false, false,
          "class Point {\n\
             static origin = 'O';\n\
             count = 0;\n\
             constructor(x, y) { this.x = x; this.y = y; }\n\
             get sum() { return this.x + this.y; }\n\
             set sum(v) { this.x = v; }\n\
             dist() { return Math.abs(this.x - this.y); }\n\
             static make() { return new Point(1, 2); }\n\
           }\n\
           var p = new Point(3, 7);\n\
           p.sum = 100;\n\
           console.log(p, p.sum, p.dist(), Point.make().sum, Point.origin, typeof Point,\n\
           Point.name, Point.length, p instanceof Point, Object.keys(p),\n\
           Point.prototype.constructor === Point, Object.getOwnPropertyNames(Point.prototype));"),
        m("class-derived", false, false,
          "class A {\n\
             constructor(v) { this.v = v; }\n\
             who() { return 'A' + this.v; }\n\
           }\n\
           class B extends A {\n\
             tag = 'b';\n\
             constructor() { super(7); this.post = this.v + 1; }\n\
             who() { return 'B/' + super.who() + '/' + this.tag; }\n\
           }\n\
           var b = new B();\n\
           console.log(b, b.who(), b instanceof A, b instanceof B,\n\
           Object.getPrototypeOf(B) === A, Object.getPrototypeOf(B.prototype) === A.prototype);"),
        m("class-default-derived-ctor", false, false,
          "class A { constructor(a, b) { this.s = a + b; } }\n\
           class B extends A {}\n\
           class C extends B { f = this.s * 2; }\n\
           console.log(new B(1, 2), new C(3, 4), B.length, new B(5, 5) instanceof A);"),
        m("class-ctor-errors", false, false,
          "class A {}\n\
           class C extends A { constructor() { this.x = 1; super(); } }\n\
           class E extends A { constructor() { super(); super(); } }\n\
           class R extends A { constructor() { super(); return 5; } }\n\
           var t1 = false, t2 = false, t3 = false, t4 = false;\n\
           try { A(); } catch (e) { t1 = e instanceof TypeError; }\n\
           try { new C(); } catch (e) { t2 = e instanceof ReferenceError; }\n\
           try { new E(); } catch (e) { t3 = e instanceof ReferenceError; }\n\
           try { new R(); } catch (e) { t4 = e instanceof TypeError; }\n\
           console.log(t1, t2, t3, t4);"),
        m("class-expressions-tdz", false, false,
          "var C = class Named { m() { return Named === C; } };\n\
           var Anon = class {};\n\
           var t1 = false;\n\
           try { D; } catch (e) { t1 = e instanceof ReferenceError; }\n\
           class D {}\n\
           console.log(C.name, Anon.name, new C().m(), t1, (class {}).name);"),
        m("class-extends-natives", false, false,
          "class MyErr extends Error { constructor(m) { super(m); this.tagged = true; } }\n\
           var e = new MyErr('x');\n\
           class MyArr extends Array {}\n\
           var a = new MyArr(3);\n\
           a.push(9);\n\
           console.log(e instanceof MyErr, e instanceof Error, e.tagged, e.message, e.name,\n\
           a.length, a instanceof MyArr, a instanceof Array, Array.isArray(a), a[3]);"),
        m("class-computed-and-symbol-keys", false, false,
          "var key = Symbol('m');\n\
           class K {\n\
             [key]() { return 5; }\n\
             ['computed']() { return 6; }\n\
             static [`st${'atic'}`]() { return 7; }\n\
             get ['g']() { return 8; }\n\
           }\n\
           var k = new K();\n\
           console.log(k[key](), k.computed(), K.static(), k.g,\n\
           Object.getOwnPropertyNames(K.prototype), Object.getOwnPropertySymbols(K.prototype).length);"),
        m("class-member-attributes", false, false,
          "class C { m() {} get a() { return 1; } static s() {} }\n\
           var md = Object.getOwnPropertyDescriptor(C.prototype, 'm');\n\
           var ad = Object.getOwnPropertyDescriptor(C.prototype, 'a');\n\
           var pd = Object.getOwnPropertyDescriptor(C, 'prototype');\n\
           console.log(md.enumerable, md.writable, md.configurable, ad.enumerable, typeof ad.get,\n\
           ad.set === undefined, pd.writable, pd.enumerable, pd.configurable,\n\
           C.prototype.m.name, C.prototype.m.length, Object.getOwnPropertyDescriptor(C, 's').enumerable);"),
        m("class-extends-null", false, false,
          "class N extends null { constructor() { return Object.create(N.prototype); } }\n\
           console.log(Object.getPrototypeOf(N.prototype), Object.getPrototypeOf(N) === Function.prototype,\n\
           new N() instanceof N);"),
        m("class-field-initializer-order", false, false,
          "var log = [];\n\
           class A { constructor() { log.push('A-ctor'); } }\n\
           class B extends A {\n\
             f1 = (log.push('f1'), 1);\n\
             constructor() { log.push('pre-super'); super(); log.push('post-super'); this.f2 = 2; }\n\
           }\n\
           var b = new B();\n\
           console.log(log, b.f1, b.f2, Object.keys(b));"),
        m("class-static-field-this", false, false,
          "class C {\n\
             static base = 10;\n\
             static derived = this.base * 2;\n\
             static fn = function () { return 'fn'; };\n\
           }\n\
           console.log(C.derived, C.fn.name, C.fn(), Object.keys(new C()).length);"),
        m("class-getter-setter-super", false, false,
          "class A { get v() { return 10; } m() { return 'a'; } }\n\
           class B extends A {\n\
             get v() { return super.v + 1; }\n\
             m() { return super.m() + 'b'; }\n\
             probe() { super.missing; return super['m'](); }\n\
           }\n\
           var b = new B();\n\
           console.log(b.v, b.m(), b.probe());"),
        m("object-literal-super", false, false,
          "var proto = { greet() { return 'p'; } };\n\
           var o = { __proto__: proto, greet() { return 'o+' + super.greet(); } };\n\
           var alt = { greet() { return 'alt'; } };\n\
           Object.setPrototypeOf(o, alt);\n\
           console.log(o.greet());"),
        // ---- S1b: Reflect ---------------------------------------------
        m("reflect-basics", false, false,
          "var o = { x: 1 };\n\
           console.log(Reflect.get(o, 'x'), Reflect.has(o, 'x'), Reflect.set(o, 'y', 2), o.y,\n\
           Reflect.deleteProperty(o, 'x'), 'x' in o,\n\
           Reflect.defineProperty(o, 'z', { value: 3 }), o.z,\n\
           Reflect.ownKeys({ b: 1, 0: 2, a: 3 }), Reflect.getPrototypeOf([]) === Array.prototype,\n\
           Reflect.isExtensible({}), Reflect.preventExtensions(o), Reflect.isExtensible(o),\n\
           Object.prototype.toString.call(Reflect));"),
        m("reflect-apply-construct", false, false,
          "function C(v) { this.v = v; } function B() {} B.prototype.kind = 'B';\n\
           var inst = Reflect.construct(C, [9], B);\n\
           var t = false; try { Reflect.construct(function () {}, 1); } catch (e) { t = e instanceof TypeError; }\n\
           console.log(Reflect.apply(function (a) { return this.base + a; }, { base: 10 }, [5]),\n\
           inst.v, inst.kind, Object.getPrototypeOf(inst) === B.prototype, t,\n\
           Reflect.construct(C, [1]).v);"),
        m("reflect-get-set-receiver", false, false,
          "var src = { get p() { return this.tag; }, set q(v) { this.written = v; } };\n\
           var rec = { tag: 't' };\n\
           Reflect.set(src, 'q', 5, rec);\n\
           console.log(Reflect.get(src, 'p', rec), rec.written, 'written' in src,\n\
           Reflect.set({}, 'k', 1, 'prim'), Reflect.getOwnPropertyDescriptor({ a: 1 }, 'a'));"),
        // ---- S1b: tagged templates ------------------------------------
        m("tagged-templates", false, false,
          "function tag(strings) {\n\
             var subs = Array.prototype.slice.call(arguments, 1);\n\
             return strings.join('|') + '#' + strings.raw.join('|') + '#' + subs.join(',');\n\
           }\n\
           var cache; function idTag(s) { var same = cache === s; cache = s; return same; }\n\
           function runTwice() { return idTag`x${1}`; }\n\
           runTwice();\n\
           console.log(tag`a\\n${1}b${2}`, runTwice(), Object.isFrozen(cache), Object.isFrozen(cache.raw),\n\
           tag`\\unicode escapes ${'ok'}`);"),
        m("super-this-tdz-orders", false, false,
          "class Base { constructor() { throw new Error('base ran'); } }\n\
           var r = [];\n\
           function t(mk) { try { mk(); r.push('none'); } catch (e) { r.push(e.constructor.name); } }\n\
           t(function () { class D extends Base { constructor() { return super[super()]; } } new D(); });\n\
           t(function () { class D extends Base { constructor() { super[super()](); } } new D(); });\n\
           t(function () { class D extends Base { constructor() { delete super[(super(), 0)]; } } new D(); });\n\
           t(function () { class D extends Base { constructor() { super.x = 1; } } new D(); });\n\
           console.log(r);"),
        // ---- S1c: collections -----------------------------------------
        m("map-set-basics", false, false,
          "var m = new Map([[1, 'a'], [-0, 'z'], [NaN, 'n']]);\n\
           m.set('k', 7);\n\
           var order = []; m.forEach(function (v, k, mm) { order.push(v, mm === m); });\n\
           var acc = []; for (var e of m) acc.push(e[0], e[1]);\n\
           var s = new Set('aba'); s.add('c');\n\
           console.log(m, m.size, m.get(0), m.get(NaN), m.delete(1), m.delete(1), order, acc,\n\
           s, s.size, [...s], Array.from(new Map([['q', 1]])), new Map(m).size,\n\
           Object.prototype.toString.call(m), m instanceof Map);"),
        m("map-set-identities-errors", false, false,
          "var t1 = false; try { Map(); } catch (e) { t1 = e instanceof TypeError; }\n\
           var t2 = false; try { new Map([1]); } catch (e) { t2 = e instanceof TypeError; }\n\
           var t3 = false; try { Map.prototype.get.call({}, 1); } catch (e) { t3 = e instanceof TypeError; }\n\
           var sd = Object.getOwnPropertyDescriptor(Map.prototype, 'size');\n\
           console.log(t1, t2, t3, Map.prototype[Symbol.iterator] === Map.prototype.entries,\n\
           Set.prototype.keys === Set.prototype.values, typeof sd.get, sd.set, sd.get.name,\n\
           Map.name, Map.length, Map.prototype.set.length, new Map(null).size);\n\
           class MyMap extends Map {}\n\
           var mm = new MyMap([[1, 2]]);\n\
           console.log(mm instanceof MyMap, mm.get(1), Object.getPrototypeOf(mm) === MyMap.prototype);"),
        m("weak-collections", false, false,
          "var wm = new WeakMap(); var k = {};\n\
           var t1 = false; try { wm.set(1, 2); } catch (e) { t1 = e instanceof TypeError; }\n\
           var sym = Symbol('s');\n\
           var t2 = false; try { new WeakMap().set(Symbol.for('r'), 1); } catch (e) { t2 = e instanceof TypeError; }\n\
           var ws = new WeakSet([k]);\n\
           console.log(wm.set(k, 1) === wm, wm.get(k), wm.has(k), wm.delete(k), wm.has(k),\n\
           t1, new WeakMap().set(sym, 9).get(sym), t2, ws.has(k), ws.delete(k), ws.has(k),\n\
           new WeakMap([[k, 2]]).get(k), Object.prototype.toString.call(wm), wm);"),
        // ---- S1c: Date ------------------------------------------------
        m("date-deterministic-clock", false, false,
          "console.log(Date.now(), new Date().getTime(), Date(), Date.now());"),
        m("date-ctor-getters", false, false,
          "var d = new Date(2023, 5, 15, 12, 30, 45, 678);\n\
           console.log(d, d.getFullYear(), d.getMonth(), d.getDate(), d.getDay(), d.getHours(),\n\
           d.getMinutes(), d.getSeconds(), d.getMilliseconds(), d.getTimezoneOffset(),\n\
           d.getUTCHours(), new Date(99, 0).getFullYear(), new Date(1.5).getTime(),\n\
           new Date(2023, 13, 32, 25, 61, 61, 1001).toISOString(), new Date(new Date(5)).getTime(),\n\
           new Date(8.64e15).getTime(), new Date(8.64e15 + 1).getTime());"),
        m("date-strings-setters", false, false,
          "var d = new Date(1700000000123);\n\
           console.log(d.toString(), d.toUTCString(), d.toDateString(), d.toTimeString(), d.toISOString(),\n\
           d.toJSON(), String(d), d + '!', +d, JSON.stringify(d));\n\
           d.setFullYear(2024, 5, 20); console.log(d.toISOString(), d.setTime(456));\n\
           var inv = new Date(NaN);\n\
           var t = false; try { inv.toISOString(); } catch (e) { t = e instanceof RangeError; }\n\
           console.log(inv.toString(), inv.toJSON(), t, inv.setHours(5));\n\
           var inv2 = new Date(NaN); inv2.setFullYear(2023); console.log(inv2.toISOString());"),
        m("date-parse-utc", false, false,
          "console.log(Date.parse('2023-11-14T22:13:20.123Z'), Date.parse('2023-11-14'),\n\
           Date.parse('2023-11-14T22:13:20'), Date.parse('2023-11-14T22:13:20+05:30'),\n\
           Date.parse('2023-02-29'), Date.parse('+275760-09-13T00:00:00.000Z'),\n\
           new Date('2023-11-14').getTime(), Date.UTC(2023, 0), Date.UTC(), Date.UTC(99, 0),\n\
           new Date(2023, 0, 15).getYear(), Date.prototype.toGMTString === Date.prototype.toUTCString);"),
        m("date-wrapper-surface", false, false,
          "console.log(Date.length, Date.name, Object.getOwnPropertyNames(Date),\n\
           Date.prototype.constructor === Date, Date.prototype.constructor.length,\n\
           Date.prototype.constructor.parse === Date.parse, Date.now.name, Date.now.length);\n\
           class D extends Date { constructor() { super(7); } }\n\
           var d = new D();\n\
           console.log(Object.getPrototypeOf(d) === Date.prototype, d instanceof D, d instanceof Date, d.getTime());"),
        // ---- S1c: JSON ------------------------------------------------
        m("json-parse-full", false, false,
          "var o = JSON.parse('{\"b\": 1, \"0\": \"z\", \"a\": [1.5e2, true, null], \"b\": 2}');\n\
           console.log(o, Object.keys(o), JSON.parse('\"\\\\u0041\\\\n\"'), JSON.parse('-0'),\n\
           1 / JSON.parse('-0'), JSON.parse('1e-7'), JSON.parse('1e400'), JSON.parse('  [ ]  '));\n\
           var ts = [];\n\
           for (var src of ['{', '01', '[1,]', '{\"a\":}', 'undefined', '1 2', '{a:1}']) {\n\
           try { JSON.parse(src); ts.push('ok'); } catch (e) { ts.push(e instanceof SyntaxError); }\n\
           }\n\
           console.log(ts);"),
        m("json-parse-reviver", false, false,
          "var log = [];\n\
           var r = JSON.parse('{\"a\": 1, \"b\": [2, 3]}', function (k, v) {\n\
           log.push(k + ':' + arguments.length + ':' + (arguments[2] && arguments[2].source));\n\
           if (k === 'a') return undefined;\n\
           return typeof v === 'number' ? v * 10 : v;\n\
           });\n\
           console.log(log, 'a' in r, r);\n\
           var srcs = [];\n\
           JSON.parse('[1, 2, 3]', function (k, v) { if (k === '0') this[1] = 99; srcs.push(arguments[2].source); return v; });\n\
           console.log(srcs);"),
        m("json-stringify-full", false, false,
          "console.log(JSON.stringify({a: 1, b: [1, {c: 2}], d: 'x'}, null, 2),\n\
           JSON.stringify([1, 'a'], null, '--'), JSON.stringify({a: {b: 1}}, null, 12),\n\
           JSON.stringify({a: 1, b: 2, 0: 'z'}, ['b', 'a', 'b', new String('a'), new Number(0)]),\n\
           JSON.stringify({a: 1, b: [2, 3]}, function (k, v) { return typeof v === 'number' ? v * 10 : v; }),\n\
           JSON.stringify({t: {toJSON: function (key) { return [key, this !== undefined]; }}}),\n\
           JSON.stringify(undefined), JSON.stringify({u: undefined, f: function () {}, s: Symbol('x')}),\n\
           JSON.stringify([undefined, function () {}, Symbol('x')]),\n\
           JSON.stringify(new Number(5)), JSON.stringify(new String('q')), JSON.stringify(new Boolean(true)),\n\
           JSON.stringify(-0), JSON.stringify({a: [, 2]}), JSON.stringify(5, 'notafn'));\n\
           var c = {}; c.self = c;\n\
           var t = false; try { JSON.stringify(c); } catch (e) { t = e instanceof TypeError; }\n\
           console.log(t, JSON.stringify('a\\u0001\"\\\\'));"),
        // ---- S1c: RegExp skeleton -------------------------------------
        m("regex-skeleton", false, false,
          "var r = /ab/g;\n\
           console.log(r, typeof r, r instanceof RegExp, r.source, r.flags, r.global, r.sticky,\n\
           r.lastIndex, /a\\/b/.source, /[/]/.source, /a/dgimsuy.flags, '' + /x/gi,\n\
           Object.prototype.toString.call(/x/), Object.getOwnPropertyNames(/x/), JSON.stringify(/x/));\n\
           r.lastIndex = 42;\n\
           var d = Object.getOwnPropertyDescriptor(r, 'lastIndex');\n\
           console.log(d, RegExp.prototype.source, RegExp.prototype.flags, RegExp.prototype.global,\n\
           typeof RegExp, RegExp.name, RegExp.length, RegExp.prototype.constructor === RegExp);\n\
           var t1 = false; try { 'a'.includes(/a/); } catch (e) { t1 = e instanceof TypeError; }\n\
           console.log(t1);"),
        // ---- S1c: Proxy binding + URI ---------------------------------
        m("proxy-binding-uri", false, false,
          "var t = false; try { Proxy({}, {}); } catch (e) { t = e instanceof TypeError; }\n\
           console.log(typeof Proxy, Proxy.name, Proxy.length, t, Object.getOwnPropertyDescriptor(Proxy, 'prototype'));\n\
           console.log(encodeURIComponent(\"Aa0-_.!~*'()\"), encodeURIComponent('#;/?:@&=+$,'),\n\
           encodeURI('#;/?:@&=+$,'), encodeURI('a b'), encodeURIComponent('\\u00e9'),\n\
           decodeURIComponent('%41%42'), decodeURI('a%20b%2Fc'), decodeURIComponent('a%20b%2Fc'),\n\
           decodeURIComponent('%c3%a9'));\n\
           var u = [];\n\
           function tc(f) { try { f(); u.push('ok'); } catch (e) { u.push(e instanceof URIError); } }\n\
           tc(function () { encodeURIComponent('\\ud800'); });\n\
           tc(function () { decodeURIComponent('%'); });\n\
           tc(function () { decodeURIComponent('%C0%80'); });\n\
           console.log(u);"),
        // ---- S1b: iteration TypeErrors --------------------------------
        m("iteration-type-errors", false, false,
          "var t1 = false, t2 = false, t3 = false;\n\
           try { for (var v of {}) {} } catch (e) { t1 = e instanceof TypeError; }\n\
           try { [].concat(...5); } catch (e) { t2 = e instanceof TypeError; }\n\
           try { var [x] = { length: 1 }; } catch (e) { t3 = e instanceof TypeError; }\n\
           console.log(t1, t2, t3);"),
        // ---- S1d: RegExp runtime --------------------------------------
        m("regexp-exec-global", false, false,
          "var r = /\\d/g; var o = []; var m; while ((m = r.exec('a1b2')) !== null) { o.push(m[0] + '@' + m.index + ':' + r.lastIndex); } console.log(o, r.lastIndex);"),
        m("regexp-exec-array-shape", false, false,
          "console.log(/(\\d)(x)?/.exec('a1b'), /z/.exec('abc'));"),
        m("regexp-named-indices", false, false,
          "console.log(/(?<y>\\d{4})-(?<mo>\\d{2})/d.exec('2024-05'));"),
        m("regexp-dup-named", false, false,
          "var r = /(?<a>x)|(?<a>y)/d; console.log(r.exec('x').groups, r.exec('y').groups, r.exec('x').indices.groups);"),
        m("regexp-test-lastindex", false, false,
          "var g = /a/g; var n = /a/; console.log(g.test('xax'), g.lastIndex, g.test('xax'), g.lastIndex, g.test('xax'), n.test('xax'), n.lastIndex);"),
        m("string-match", false, false,
          "console.log('a1b2c3'.match(/\\d/g), 'abc'.match(/x/g), 'a1b2'.match(/(\\d)/), 'abc'.match(/(?:)/));"),
        m("string-search", false, false,
          "console.log('abcdef'.search(/d/), 'abc'.search(/x/), 'abcdef'.search('cd'));"),
        m("string-replace-dollar", false, false,
          "console.log('abc'.replace(/b/, \"[$$|$&|$`|$']\"), 'a1b2'.replace(/(\\d)/, '<$1>'), 'x'.replace(/(a)?x/, '[$1]'), 'ab'.replace(/b/, '$2$00'));"),
        m("string-replace-named-fn", false, false,
          "console.log('2024-05'.replace(/(?<y>\\d+)-(?<mo>\\d+)/, '$<mo>/$<y>/$<zz>'), 'a1b2'.replace(/(\\d)/g, function (mm, p, o, s) { return '[' + mm + p + o + ']'; }));"),
        m("string-replaceall", false, false,
          "var t = false; try { 'x'.replaceAll(/x/, 'y'); } catch (e) { t = e instanceof TypeError; } console.log('a-b-c'.replaceAll('-', '+'), 'a1b2'.replaceAll(/\\d/g, 'X'), t);"),
        m("string-split-regex", false, false,
          "console.log('a1b2c'.split(/(\\d)/), 'a,b,c,d'.split(/,/, 2), 'abc'.split(/(?:)/), 'xax'.split(/x/), ''.split(/x/), ''.split(/(?:)/), 'a1b'.split(/\\d/));"),
        m("regexp-source-flags", false, false,
          "console.log(new RegExp('a/b').source, new RegExp('').source, new RegExp('[/]').source, /a\\/b/.source, new RegExp(/x/gi, 'm').flags, new RegExp('a', 'gy').flags, RegExp('foo').source);"),
        m("regexp-newline-source", false, false,
          "console.log(new RegExp('\\n').source.length, new RegExp('\\n').source === '\\\\n', new RegExp('a\\nb/c').source);"),
        m("regexp-constructor-same", false, false,
          "var re = /x/; console.log(new RegExp(re) === re, RegExp(re) === re, new RegExp(re, 'g').flags, RegExp(re, 'g') === re);"),
        m("regexp-subclass-split", false, false,
          "class MyRe extends RegExp {} var mr = new MyRe('-', 'g'); console.log(mr instanceof RegExp, mr instanceof MyRe, mr.source, mr.flags, 'a-b-c'.split(new MyRe('-')));"),
        // ---- S1e: private class elements ------------------------------
        m("private-class-elements", false, false,
          "class C {\n\
             #x = 1;\n\
             #m() { return this.#x; }\n\
             get #y() { return this._y || 0; }\n\
             set #y(v) { this._y = v * 2; }\n\
             static #s = 5;\n\
             run() { this.#y = 3; return [this.#m(), this.#y, this.#x]; }\n\
             static probe(o) { return #x in o; }\n\
             static getS() { return C.#s; }\n\
           }\n\
           var c = new C();\n\
           console.log(c.run(), C.getS(), C.probe(c), C.probe({}), Object.keys(c), JSON.stringify(c), c);"),
        m("private-methods-accessors-errors", false, false,
          "class C {\n\
             #m() {}\n\
             get #g() { return 3; }\n\
             set #s(v) {}\n\
             probe() {\n\
               var w = false; try { this.#m = 1; } catch (e) { w = e instanceof TypeError; }\n\
               var r = false; try { this.#s; } catch (e) { r = e instanceof TypeError; }\n\
               var ws = false; try { this.#g = 1; } catch (e) { ws = e instanceof TypeError; }\n\
               return [this.#g, w, r, ws];\n\
             }\n\
             foreign(o) { return o.#m; }\n\
           }\n\
           var c = new C();\n\
           var t = false; try { c.foreign({}); } catch (e) { t = e instanceof TypeError; }\n\
           console.log(c.probe(), t);"),
        m("private-nested-and-derived", false, false,
          "class Outer { #o = 7; make() { return class Inner { p(x) { return x.#o; } }; } }\n\
           var I = new Outer().make();\n\
           class Base { constructor(o) { return o; } }\n\
           class D extends Base { #x = 1; constructor(o) { super(o); } }\n\
           var shared = {}; new D(shared);\n\
           var dbl = false; try { new D(shared); } catch (e) { dbl = e instanceof TypeError; }\n\
           console.log(new I().p(new Outer()), dbl);"),
        // ---- S1e: user-defined iterator protocol ----------------------
        m("user-iterator-protocol", false, false,
          "var closed = 0;\n\
           function mk() { var i = 0; return { [Symbol.iterator]() { return {\n\
             next() { return { value: i, done: i++ >= 5 }; },\n\
             return() { closed++; return {}; } }; } }; }\n\
           var out = []; for (var x of mk()) { out.push(x); if (x === 2) break; }\n\
           var spread = [...mk()];\n\
           var [a, b] = mk();\n\
           var m = new Map([[0, 'z']]); var mm = new Map(mk2entries());\n\
           function mk2entries() { var i = 0; return { [Symbol.iterator]() { return { next() { return { value: [i, i * 10], done: i++ >= 2 }; } }; } }; }\n\
           console.log(out, spread, a, b, closed, Array.from(mk()), mm.get(1));"),
        m("user-iterator-close-throw", false, false,
          "var log = [];\n\
           var it = { [Symbol.iterator]() { return {\n\
             next() { return { value: 1, done: false }; },\n\
             return() { log.push('closed'); return {}; } }; } };\n\
           var caught = '';\n\
           try { for (var x of it) { throw 'body-err'; } } catch (e) { caught = e; }\n\
           var t = false; try { for (var y of it) break; } catch (e) { t = 'unexpected'; }\n\
           console.log(caught, log, t);"),
        // ---- S1e: generators ------------------------------------------
        m("gen-basic-sequence", false, false,
          "function* g(a) { yield a + 1; yield a + 2; return a + 3; }\n\
           var it = g(10);\n\
           var r1 = it.next(), r2 = it.next(), r3 = it.next(), r4 = it.next();\n\
           console.log(r1.value, r1.done, r2.value, r2.done, r3.value, r3.done, r4.value, r4.done);"),
        m("gen-next-value-roundtrip", false, false,
          "function* g() { var x = yield 1; var y = yield x + 10; return x + y; }\n\
           var it = g();\n\
           console.log(it.next().value, it.next(5).value, it.next(100).value, it.next().value);"),
        m("gen-yield-positions", false, false,
          "function* g() { let a = yield 1; a = yield a; yield; return (yield 9); }\n\
           var it = g();\n\
           var o = [];\n\
           o.push(it.next().value); o.push(it.next(2).value); o.push(it.next(3).value);\n\
           o.push(it.next(4).value); var last = it.next(7);\n\
           console.log(o, last.value, last.done);"),
        m("gen-loops", false, false,
          "function* g() { for (var i = 0; i < 3; i++) yield i; var j = 0; while (j < 2) { yield 'w' + j; j++; } }\n\
           console.log([...g()]);"),
        m("gen-for-of-body", false, false,
          "function* g(arr) { for (var x of arr) { yield x * 2; } }\n\
           var out = []; for (var v of g([1, 2, 3])) out.push(v);\n\
           console.log(out, Array.from(g([4, 5])));"),
        m("gen-delegation", false, false,
          "function* inner() { yield 1; yield 2; return 'inner-ret'; }\n\
           function* outer() { var r = yield* inner(); yield r; yield* [7, 8]; }\n\
           console.log([...outer()]);"),
        m("gen-delegation-next-thread", false, false,
          "function* inner() { var a = yield 'a'; var b = yield 'b'; return a + b; }\n\
           function* outer() { var got = yield* inner(); yield got; }\n\
           var it = outer();\n\
           console.log(it.next().value, it.next(10).value, it.next(20).value, it.next().value);"),
        m("gen-return-method", false, false,
          "function* g() { yield 1; yield 2; yield 3; }\n\
           var it = g();\n\
           var a = it.next(); var b = it.return(99); var c = it.next();\n\
           console.log(a.value, a.done, b.value, b.done, c.value, c.done);"),
        m("gen-throw-method", false, false,
          "function* g() { try { yield 1; } catch (e) { yield 'caught:' + e; } yield 2; }\n\
           var it = g();\n\
           console.log(it.next().value, it.throw('boom').value, it.next().value);"),
        m("gen-return-runs-finally", false, false,
          "var log = [];\n\
           function* g() { try { yield 1; yield 2; } finally { log.push('fin'); } }\n\
           var it = g();\n\
           it.next(); var r = it.return(42);\n\
           console.log(r.value, r.done, log, it.next().done);"),
        m("gen-finally-overrides-return", false, false,
          "function* g() { try { yield 1; } finally { return 'from-finally'; } }\n\
           var it = g(); it.next();\n\
           var r = it.return('ignored');\n\
           console.log(r.value, r.done);"),
        m("gen-throw-caught-in-finally-try", false, false,
          "var log = [];\n\
           function* g() { try { try { yield 1; } finally { log.push('f'); } } catch (e) { yield 'c:' + e; } }\n\
           var it = g(); it.next();\n\
           console.log(it.throw('x').value, log);"),
        m("gen-done-behaviour", false, false,
          "function* g() { yield 1; }\n\
           var it = g(); it.next(); it.next();\n\
           var n = it.next(), r = it.return(5), t;\n\
           try { it.throw('e'); } catch (e) { t = e; }\n\
           console.log(n.value, n.done, r.value, r.done, t);"),
        m("gen-start-abrupt", false, false,
          "function* g() { yield 1; }\n\
           var a = g().return(7);\n\
           var b, thrown; var it = g();\n\
           try { it.throw('nope'); } catch (e) { thrown = e; }\n\
           console.log(a.value, a.done, thrown, it.next().done);"),
        m("gen-protocol-identity", false, false,
          "function* g() { yield 1; }\n\
           var it = g();\n\
           console.log(typeof g, g.prototype !== undefined, it[Symbol.iterator]() === it,\n\
           Object.prototype.toString.call(it), Object.getPrototypeOf(it) === g.prototype,\n\
           it.constructor === Object.getPrototypeOf(g));"),
        m("gen-not-constructor", false, false,
          "function* g() { yield 1; }\n\
           var t = false; try { new g(); } catch (e) { t = e instanceof TypeError; }\n\
           console.log(t, g.prototype.constructor === Object.getPrototypeOf(g));"),
        m("gen-iter-result-shape", false, false,
          "function* g() { yield 5; }\n\
           var r = g().next();\n\
           console.log(Object.keys(r), r.value, r.done, Object.getPrototypeOf(r) === Object.prototype);"),
        m("gen-method-in-object", false, false,
          "var o = { x: 3, *gen() { yield this.x; yield this.x + 1; } };\n\
           console.log([...o.gen()]);"),
        m("gen-method-in-class", false, false,
          "class C { constructor(n) { this.n = n; } *count() { for (var i = 0; i < this.n; i++) yield i; } }\n\
           var c = new C(3);\n\
           console.log([...c.count()], Array.from(new C(2).count()));"),
        m("gen-delegation-throw-nomethod", false, false,
          "function* g() { yield* [1, 2, 3]; }\n\
           var it = g(); it.next();\n\
           var t = false; try { it.throw('e'); } catch (err) { t = err instanceof TypeError; }\n\
           console.log(t, it.next().done);"),
        m("gen-destructuring-spread", false, false,
          "function* g() { yield 1; yield 2; yield 3; }\n\
           var [a, ...rest] = g();\n\
           console.log(a, rest, Math.max(...g()));"),
        // ---- Binary data: ArrayBuffer / DataView / TypedArray ----------
        m("ta-construct-forms", false, false,
          "var a = new Int16Array(3); var b = new Int16Array([1, 2, 3]); var c = new Int16Array(b);\n\
           var ab = new ArrayBuffer(8); var d = new Int16Array(ab, 2, 2);\n\
           console.log(a.length, a[0], b[0], b[2], c[1], d.length, d.byteOffset, d.byteLength, ab.byteLength);"),
        m("ta-int-wrap", false, false,
          "var a = new Int8Array([0, 127, 128, 255, 256, -1, -128, -129, 3.9, -3.9, NaN]);\n\
           console.log(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10]);"),
        m("ta-uint-wrap", false, false,
          "var a = new Uint8Array([0, 255, 256, -1, 3.9, 300]);\n\
           var b = new Uint16Array([65535, 65536, -1, 70000]);\n\
           console.log(a[0], a[1], a[2], a[3], a[4], a[5], b[0], b[1], b[2], b[3]);"),
        m("ta-uint8clamped", false, false,
          "var a = new Uint8ClampedArray([-5, 0, 0.5, 1.5, 2.5, 254.5, 255, 255.5, 300, NaN, 127.5]);\n\
           console.log(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10]);"),
        m("ta-float32", false, false,
          "var a = new Float32Array([0.1, 1.5, 1e40, -0, NaN, 3.14159265358979]);\n\
           console.log(a[0], a[1], a[2], 1 / a[3], a[4], a[5]);"),
        m("ta-float16", false, false,
          "var a = new Float16Array([0.1, 1.5, 65504, 65520, 6e-8, 1.0004882812, -0]);\n\
           console.log(a[0], a[1], a[2], a[3], a[4], a[5], 1 / a[6]);"),
        m("ta-oob-index", false, false,
          "var a = new Int32Array([10, 20, 30]);\n\
           console.log(a[3], a[-1], a[1.5], a['foo'], 3 in a, 2 in a, -1 in a, delete a[0], a[0], delete a[9]);"),
        m("ta-define-index", false, false,
          "var a = new Int8Array(2); var ok = Reflect.defineProperty(a, '0', { value: 5 });\n\
           var bad = Reflect.defineProperty(a, '0', { value: 6, configurable: false });\n\
           var oob = Reflect.defineProperty(a, '5', { value: 7 });\n\
           console.log(ok, a[0], bad, oob, Object.getOwnPropertyDescriptor(a, '0').writable);"),
        m("ta-tostringtag", false, false,
          "var a = new Float64Array(1);\n\
           console.log(Object.prototype.toString.call(a), Object.prototype.toString.call(new DataView(new ArrayBuffer(1))),\n\
           a[Symbol.toStringTag], Int8Array.prototype[Symbol.toStringTag]);"),
        m("ta-own-keys", false, false,
          "var a = new Uint8Array([1, 2, 3]); a.foo = 'x';\n\
           console.log(Object.getOwnPropertyNames(a), Object.keys(a), a.hasOwnProperty(0), a.hasOwnProperty('foo'));"),
        m("ta-detached-transfer", false, false,
          "var ab = new ArrayBuffer(8); var a = new Int32Array(ab);\n\
           var nb = ab.transfer();\n\
           console.log(ab.detached, ab.byteLength, a.length, a[0], nb.byteLength, nb.detached);"),
        m("ta-detached-typeerror", false, false,
          "var ab = new ArrayBuffer(8); ab.transfer();\n\
           var t = false; try { new Int32Array(ab); } catch (e) { t = e instanceof TypeError; }\n\
           console.log(ab.detached, t);"),
        m("ab-resizable", false, false,
          "var ab = new ArrayBuffer(4, { maxByteLength: 16 });\n\
           console.log(ab.resizable, ab.byteLength, ab.maxByteLength);\n\
           var a = new Uint8Array(ab); a[0] = 9; ab.resize(8);\n\
           console.log(ab.byteLength, a.length, a[0], a[7]);\n\
           ab.resize(2); console.log(ab.byteLength, a.length);"),
        m("ab-slice-isview", false, false,
          "var ab = new ArrayBuffer(8); new Uint8Array(ab).set([1, 2, 3, 4, 5, 6, 7, 8]);\n\
           var s = ab.slice(2, 5); var v = new Uint8Array(s);\n\
           console.log(s.byteLength, v[0], v[2], ArrayBuffer.isView(v), ArrayBuffer.isView(ab), ArrayBuffer.isView({}));"),
        m("dataview-byteorder", false, false,
          "var dv = new DataView(new ArrayBuffer(8));\n\
           dv.setUint32(0, 0x01020304); var be = dv.getUint32(0); var le = dv.getUint32(0, true);\n\
           dv.setFloat64(0, 1.5, true); var f = dv.getFloat64(0, true);\n\
           dv.setInt16(0, -2, true); var i = dv.getInt16(0, true);\n\
           console.log(be, le, f, i, dv.byteLength, dv.byteOffset);"),
        m("dataview-bounds", false, false,
          "var dv = new DataView(new ArrayBuffer(4));\n\
           var t1 = false; try { dv.getUint32(1); } catch (e) { t1 = e instanceof RangeError; }\n\
           var t2 = false; try { dv.getInt8(4); } catch (e) { t2 = e instanceof RangeError; }\n\
           dv.setUint8(3, 200); console.log(t1, t2, dv.getUint8(3));"),
        m("ta-set-overlap", false, false,
          "var ab = new ArrayBuffer(8); var a = new Uint8Array(ab); a.set([1, 2, 3, 4, 5, 6, 7, 8]);\n\
           var b = new Uint8Array(ab, 0, 4); var c = new Uint8Array(ab, 2, 4);\n\
           c.set(b); console.log(a[0], a[1], a[2], a[3], a[4], a[5]);"),
        m("ta-set-arraylike", false, false,
          "var a = new Int16Array(5); a.set([10, 20, 30], 1);\n\
           var t = false; try { a.set([1, 2], 4); } catch (e) { t = e instanceof RangeError; }\n\
           console.log(a[0], a[1], a[2], a[3], a[4], t);"),
        m("ta-sort-default", false, false,
          "var a = new Float64Array([3, 1, NaN, 2, -0, 0, Infinity, -Infinity]);\n\
           a.sort(); console.log(a[0], a[1], a[2], a[3], 1 / a[4], 1 / a[5], a[6], a[7]);"),
        m("ta-sort-comparefn", false, false,
          "var a = new Int32Array([5, 3, 8, 1, 9, 2]);\n\
           a.sort(function (x, y) { return y - x; });\n\
           console.log(a[0], a[1], a[2], a[3], a[4], a[5]);"),
        m("ta-methods-numeric", false, false,
          "var a = new Int32Array([1, 2, 3, 4, 5]);\n\
           console.log(a.join('-'), a.indexOf(3), a.lastIndexOf(4), a.includes(5), a.at(-1),\n\
           a.reduce(function (s, x) { return s + x; }, 0), a.some(function (x) { return x > 4; }),\n\
           a.every(function (x) { return x > 0; }), a.find(function (x) { return x > 2; }));"),
        m("ta-map-filter-slice", false, false,
          "var a = new Int32Array([1, 2, 3, 4]);\n\
           var m = a.map(function (x) { return x * 2; });\n\
           var f = a.filter(function (x) { return x % 2 === 0; });\n\
           var s = a.slice(1, 3);\n\
           console.log(m[0], m[3], m.length, f[0], f[1], f.length, s[0], s[1], s.length,\n\
           m instanceof Int32Array);"),
        m("ta-fill-copywithin-reverse", false, false,
          "var a = new Uint8Array([1, 2, 3, 4, 5]); a.fill(9, 1, 3);\n\
           var b = new Uint8Array([1, 2, 3, 4, 5]); b.copyWithin(0, 3);\n\
           var c = new Uint8Array([1, 2, 3]); c.reverse();\n\
           console.log(a[0], a[1], a[2], a[3], b[0], b[1], b[2], c[0], c[2]);"),
        m("ta-subarray", false, false,
          "var a = new Int8Array([1, 2, 3, 4, 5]); var s = a.subarray(1, 4); s[0] = 99;\n\
           console.log(s.length, s[0], a[1], s.buffer === a.buffer, s.byteOffset);"),
        m("ta-from-of", false, false,
          "var a = Uint8Array.from([1, 2, 3], function (x) { return x * 10; });\n\
           var b = Int16Array.of(7, 8, 9);\n\
           console.log(a[0], a[1], a[2], a.length, b[0], b[2], b.length, b instanceof Int16Array);"),
        m("ta-species-getter", false, false,
          "console.log(Int8Array[Symbol.species] === Int8Array, ArrayBuffer.prototype.constructor === ArrayBuffer,\n\
           Object.getPrototypeOf(Int8Array) === Object.getPrototypeOf(Uint8Array),\n\
           Int8Array.BYTES_PER_ELEMENT, Float64Array.BYTES_PER_ELEMENT, Uint8Array.prototype.BYTES_PER_ELEMENT);"),
        m("ta-typeof-globals", false, false,
          "console.log(typeof Float16Array, typeof BigInt64Array, typeof Float64Array, typeof DataView,\n\
           typeof ArrayBuffer, Int8Array.name, Uint8ClampedArray.name, Float32Array.length);"),
        m("ta-for-of-spread", false, false,
          "var a = new Int16Array([5, 6, 7]); var out = [];\n\
           for (var x of a) out.push(x);\n\
           console.log(out, [...a], Math.max(...a), Array.from(a).length, Array.from(a, function (v) { return v * 2; }));"),
        m("ta-iterate-detach", false, false,
          "var ab = new ArrayBuffer(12); var a = new Int32Array(ab); a[0] = 1; a[1] = 2; a[2] = 3;\n\
           var seen = []; var t = false;\n\
           try { for (var x of a) { seen.push(x); if (x === 2) ab.transfer(); } } catch (e) { t = e instanceof TypeError; }\n\
           console.log(seen, t);"),
        m("ta-length-tracking", false, false,
          "var ab = new ArrayBuffer(8, { maxByteLength: 16 }); var a = new Uint8Array(ab);\n\
           console.log(a.length); ab.resize(12); console.log(a.length, a.byteLength);\n\
           ab.resize(4); console.log(a.length);"),
        m("ta-ctor-offset-errors", false, false,
          "var ab = new ArrayBuffer(8);\n\
           var t1 = false; try { new Int32Array(ab, 1); } catch (e) { t1 = e instanceof RangeError; }\n\
           var t2 = false; try { new Int32Array(ab, 0, 3); } catch (e) { t2 = e instanceof RangeError; }\n\
           var t3 = false; try { new Int32Array(ab, 12); } catch (e) { t3 = e instanceof RangeError; }\n\
           console.log(t1, t2, t3, new Int32Array(ab, 4).length);"),
        m("ta-proto-chain", false, false,
          "var TA = Object.getPrototypeOf(Int8Array);\n\
           console.log(TA === Object.getPrototypeOf(Float64Array), TA.name,\n\
           Object.getPrototypeOf(Int8Array.prototype) === TA.prototype,\n\
           Int8Array.prototype.constructor === Int8Array,\n\
           new Int8Array(0) instanceof TA);"),
        // ---- M2: Promise + the event loop -----------------------------
        m("promise-micro-before-macro", false, false,
          "setTimeout(() => console.log('timer'), 0);\n\
           Promise.resolve().then(() => console.log('micro'));\n\
           console.log('sync');"),
        m("promise-then-chain-order", false, false,
          "Promise.resolve(1).then(v => { console.log('a', v); return v + 1; })\n\
             .then(v => { console.log('b', v); });\n\
           Promise.resolve().then(() => console.log('c'));\n\
           console.log('sync');"),
        m("promise-executor-resolve-reject", false, false,
          "new Promise((res) => res(42)).then(v => console.log('r', v));\n\
           new Promise((_, rej) => rej('x')).catch(e => console.log('c', e));\n\
           new Promise(() => { throw 'boom'; }).catch(e => console.log('t', e));\n\
           console.log('sync');"),
        m("promise-all-order", false, false,
          "Promise.all([Promise.resolve(3), 2, Promise.resolve(1)])\n\
             .then(a => console.log(a[0], a[1], a[2], a.length));\n\
           Promise.all([]).then(a => console.log('empty', a.length));"),
        m("promise-allsettled", false, false,
          "Promise.allSettled([Promise.resolve(1), Promise.reject('e')])\n\
             .then(a => console.log(a[0].status, a[0].value, a[1].status, a[1].reason));"),
        m("promise-race-any", false, false,
          "Promise.race([Promise.resolve('win'), Promise.reject('lose')])\n\
             .then(v => console.log('race', v), e => console.log('raceE', e));\n\
           Promise.any([Promise.reject('a'), Promise.resolve('b')])\n\
             .then(v => console.log('any', v));"),
        m("promise-thenable-assimilation", false, false,
          "var thenable = { then(res) { res('assim'); } };\n\
           Promise.resolve(thenable).then(v => console.log('v', v));\n\
           console.log('sync');"),
        m("promise-finally", false, false,
          "Promise.resolve('ok').finally(() => console.log('fin1')).then(v => console.log('val', v));\n\
           Promise.reject('bad').finally(() => console.log('fin2')).catch(e => console.log('err', e));\n\
           console.log('sync');"),
        // ---- Promise static methods honoring a subclass / custom receiver C --
        m("promise-subclass-resolve", false, false,
          "var executor = null, callCount = 0;\n\
           class SubP extends Promise { constructor(a){ super(a); executor = a; callCount++; } }\n\
           var r = SubP.resolve(5);\n\
           console.log(r.constructor === SubP, r instanceof SubP, callCount, typeof executor);"),
        m("promise-subclass-resolve-passthrough", false, false,
          "class SubP extends Promise {}\n\
           var a = SubP.resolve(5);\n\
           console.log(SubP.resolve(a) === a);"),
        m("promise-subclass-all-empty", false, false,
          "var callCount = 0;\n\
           class SubP extends Promise { constructor(a){ super(a); callCount++; } }\n\
           var r = SubP.all([]);\n\
           console.log(r.constructor === SubP, r instanceof SubP, callCount);"),
        m("promise-subclass-race-empty", false, false,
          "class SubP extends Promise {}\n\
           var r = SubP.race([]);\n\
           console.log(r instanceof SubP, typeof r.then);"),
        m("promise-subclass-withresolvers", false, false,
          "class SubP extends Promise {}\n\
           var o = SubP.withResolvers.call(SubP);\n\
           console.log(o.promise instanceof SubP, typeof o.resolve, typeof o.reject);"),
        m("promise-all-custom-ctor-resolve-element", false, false,
          "var order = [];\n\
           function C(exec){ function resolve(vals){ order.push('r:' + vals.length + ':' + vals[0]); } exec(resolve, function(){}); }\n\
           C.resolve = function(v){ return v; };\n\
           var p1 = { then: function(onF){ onF('X'); onF('Y'); } };\n\
           Promise.all.call(C, [p1]);\n\
           console.log(order.join('|'));"),
        m("promise-all-ctx-non-ctor-throws", false, false,
          "var threw = false;\n\
           try { Promise.all.call(eval, []); } catch (e) { threw = e instanceof TypeError; }\n\
           console.log(threw);"),
        m("queue-microtask", false, false,
          "queueMicrotask(() => console.log('mt1'));\n\
           Promise.resolve().then(() => console.log('p1'));\n\
           queueMicrotask(() => console.log('mt2'));\n\
           console.log('sync');"),
        m("settimeout-ordering-args", false, false,
          "setTimeout((a, b) => console.log('t', a, b), 10, 'x', 'y');\n\
           setTimeout(() => console.log('early'), 5);\n\
           var id = setTimeout(() => console.log('cancelled'), 1);\n\
           clearTimeout(id);\n\
           console.log('sync');"),
        // ---- M2: async / await ----------------------------------------
        m("async-await-tick-order", false, false,
          "async function f() { console.log('1'); await null; console.log('2'); await null; console.log('3'); return 'r'; }\n\
           f().then(v => console.log('done', v)); console.log('sync');"),
        m("async-try-catch-await", false, false,
          "async function g() {\n\
             try { await Promise.reject('boom'); console.log('unreached'); }\n\
             catch (e) { console.log('caught', e); }\n\
             return 'ok';\n\
           }\n\
           g().then(v => console.log('done', v));"),
        m("async-returns-promise", false, false,
          "async function h() { return Promise.resolve('inner'); }\n\
           h().then(v => console.log('v', v));\n\
           console.log(typeof h, h() instanceof Promise);"),
        m("async-arrow-and-loop", false, false,
          "var run = async (n) => { let s = 0; for (let i = 0; i < n; i++) { await null; console.log('i', i); } return s; };\n\
           run(3).then(v => console.log('done', v));"),
        m("async-throw-rejects", false, false,
          "async function boom() { await null; throw new TypeError('x'); }\n\
           boom().then(() => console.log('no'), e => console.log('rej', e instanceof TypeError));"),
        m("async-fn-not-constructor", false, false,
          "async function foo() {}\n\
           var t1 = false; try { new foo(); } catch (e) { t1 = e instanceof TypeError; }\n\
           var AF = Object.getPrototypeOf(foo).constructor;\n\
           var inst = AF();\n\
           var t2 = false; try { new inst(); } catch (e) { t2 = e instanceof TypeError; }\n\
           console.log(t1, t2, AF.name, inst.length, inst.name, typeof inst);"),
        m("async-function-dynamic-ctor", false, false,
          "var AF = async function(){}.constructor;\n\
           var f1 = AF('a', 'await 1;');\n\
           var f2 = AF('a,b', 'await 1;');\n\
           var f3 = AF('a', 'b', 'await 1;');\n\
           var f4 = new AF('a', 'await 1;');\n\
           console.log(f1.length, f2.length, f3.length, f4.length, f1.name, typeof f1,\n\
           AF.name, AF.length, Object.getPrototypeOf(f1) === AF.prototype);"),
        // ---- M2: async class methods + async generators (§27.6) --------
        m("async-class-method", false, false,
          "class C { async m(x) { var y = await Promise.resolve(1); return x + y; } }\n\
           new C().m(10).then(v => console.log('v', v)); console.log('sync');"),
        m("async-class-method-static-private", false, false,
          "class C {\n\
             static async s(x) { var v = await Promise.resolve(x); return 'S' + v; }\n\
             async #p(x) { var v = await Promise.resolve(x); return 'P' + v; }\n\
             call(x) { return this.#p(x); }\n\
           }\n\
           C.s(1).then(v => console.log(v));\n\
           new C().call(2).then(v => console.log(v));"),
        m("async-obj-method", false, false,
          "var o = { async m() { return await Promise.resolve(42); } };\n\
           o.m().then(v => console.log('v', v));"),
        m("asyncgen-basic-next", false, false,
          "async function* g() { yield 1; yield 2; yield 3; }\n\
           var it = g();\n\
           it.next().then(r => console.log('a', r.value, r.done));\n\
           it.next().then(r => console.log('b', r.value, r.done));\n\
           it.next().then(r => console.log('c', r.value, r.done));\n\
           it.next().then(r => console.log('d', r.value, r.done));\n\
           console.log('sync');"),
        m("asyncgen-await-inside", false, false,
          "async function* g() { var x = await Promise.resolve(10); yield x; yield await Promise.resolve(20); }\n\
           var it = g();\n\
           it.next().then(r => console.log('r1', r.value));\n\
           it.next().then(r => console.log('r2', r.value));\n\
           it.next().then(r => console.log('r3', r.value, r.done));"),
        m("asyncgen-body-throw", false, false,
          "async function* g() { yield 1; throw new Error('boom'); }\n\
           var it = g();\n\
           it.next().then(r => console.log('n1', r.value));\n\
           it.next().then(r => console.log('n2'), e => console.log('rej', e.message));\n\
           it.next().then(r => console.log('n3', r.value, r.done));"),
        m("asyncgen-yield-expr-value", false, false,
          "async function* g() { var a = yield 1; var b = yield a + 1; return a + b; }\n\
           var it = g();\n\
           it.next().then(r => console.log('a', r.value, r.done));\n\
           it.next(10).then(r => console.log('b', r.value, r.done));\n\
           it.next(20).then(r => console.log('c', r.value, r.done));"),
        m("asyncgen-for-loop-yield", false, false,
          "class C { async *nums(n) { for (var i = 0; i < n; i++) yield i * 10; } }\n\
           var it = new C().nums(3);\n\
           it.next().then(r => console.log(r.value));\n\
           it.next().then(r => console.log(r.value));\n\
           it.next().then(r => console.log(r.value));\n\
           it.next().then(r => console.log('done', r.done));"),
        m("asyncgen-identity", false, false,
          "async function* g() {}\n\
           var it = g();\n\
           console.log(typeof g, g.constructor.name, typeof it[Symbol.asyncIterator],\n\
           it[Symbol.asyncIterator]() === it, typeof it.next, typeof it.return, typeof it.throw,\n\
           Object.getPrototypeOf(g).constructor === g.constructor,\n\
           Object.prototype.toString.call(it));"),
        m("asyncgen-obj-method-tostring", false, false,
          "var o = { async *gen() { yield 1; } };\n\
           console.log(Object.prototype.toString.call(o.gen()));"),
        m("asyncgen-completed-next", false, false,
          "async function* g() { yield 1; }\n\
           var it = g();\n\
           it.next().then(r => console.log('1', r.value, r.done));\n\
           it.next().then(r => console.log('2', r.value, r.done));\n\
           it.next().then(r => console.log('3', r.value, r.done));"),
        m("asyncgen-return-awaits", false, false,
          "async function* g() { return 5; }\n\
           g().next().then(r => console.log('ret', r.value, r.done));\n\
           Promise.resolve().then(() => console.log('p1')).then(() => console.log('p2'));\n\
           console.log('sync');"),
        m("asyncgen-return-thenable", false, false,
          "async function* g() { return { then(res) { res(99); } }; }\n\
           g().next().then(r => console.log('v', typeof r.value, r.value, r.done));"),
        m("asyncgen-throw-at-start", false, false,
          "async function* g() { yield 1; }\n\
           var it = g();\n\
           it.throw(new Error('early')).then(() => console.log('no'), e => console.log('rej', e.message));\n\
           it.next().then(r => console.log('after', r.value, r.done));"),
        m("asyncgen-fdi-throw-sync", false, false,
          "async function* g(x = (function(){ throw new Error('p') })()) { yield 1; }\n\
           try { g(); console.log('no-throw'); } catch (e) { console.log('caught', e.message); }"),
        // ---- §10.5: Proxy exotic objects + the 13 traps ----------------
        m("proxy-traps-invoked-args", false, false,
          "var log = [];\n\
           var t = { x: 1 };\n\
           var p = new Proxy(t, {\n\
             get(tt, k, r) { log.push('get:' + String(k)); return tt[k]; },\n\
             has(tt, k) { log.push('has:' + String(k)); return k in tt; },\n\
             set(tt, k, v, r) { log.push('set:' + String(k)); tt[k] = v; return true; },\n\
             deleteProperty(tt, k) { log.push('del:' + String(k)); delete tt[k]; return true; }\n\
           });\n\
           var a = p.x; var b = ('x' in p); p.y = 2; delete p.x;\n\
           console.log(a, b, t.y, 'x' in t, log.join('|'));"),
        m("proxy-fall-through-empty-handler", false, false,
          "var t = { a: 1 }; Object.defineProperty(t, 'b', { value: 2, enumerable: false });\n\
           var p = new Proxy(t, {});\n\
           console.log(p.a, p.b, 'a' in p, Object.keys(p).join(','), Reflect.ownKeys(p).join(','),\n\
           Object.getOwnPropertyDescriptor(p, 'b').enumerable, Object.getPrototypeOf(p) === Object.prototype,\n\
           Object.isExtensible(p), Array.isArray(new Proxy([1], {})));"),
        m("proxy-reflect-default-roundtrip", false, false,
          "var t = {};\n\
           console.log(Reflect.set(t, 'k', 5), Reflect.get(t, 'k'), Reflect.has(t, 'k'),\n\
           Reflect.deleteProperty(t, 'k'), Reflect.has(t, 'k'),\n\
           Reflect.defineProperty(t, 'z', { value: 9, enumerable: true }), t.z,\n\
           Reflect.ownKeys(t).join(','), Reflect.getPrototypeOf(t) === Object.prototype);"),
        m("proxy-get-invariant-nonconfig-nonwritable", false, false,
          "var t = {}; Object.defineProperty(t, 'x', { value: 10, writable: false, configurable: false });\n\
           var p = new Proxy(t, { get() { return 999; } });\n\
           var ok = false; try { p.x; } catch (e) { ok = e instanceof TypeError; }\n\
           var p2 = new Proxy(t, { get() { return 10; } });\n\
           console.log(ok, p2.x);"),
        m("proxy-gopd-invariant-report-absent", false, false,
          "var t = {}; Object.defineProperty(t, 'x', { value: 1, configurable: false });\n\
           var p = new Proxy(t, { getOwnPropertyDescriptor() { return undefined; } });\n\
           var ok = false; try { Object.getOwnPropertyDescriptor(p, 'x'); } catch (e) { ok = e instanceof TypeError; }\n\
           var t2 = {}; var p2 = new Proxy(t2, { getOwnPropertyDescriptor() { return { value: 7, configurable: true }; } });\n\
           var d = Object.getOwnPropertyDescriptor(p2, 'y');\n\
           console.log(ok, d.value, d.writable, d.enumerable, d.configurable);"),
        m("proxy-ownkeys-invariants", false, false,
          "var t = {}; Object.defineProperty(t, 'x', { value: 1, configurable: false, enumerable: true });\n\
           var missing = new Proxy(t, { ownKeys() { return []; } });\n\
           var ok1 = false; try { Object.keys(missing); } catch (e) { ok1 = e instanceof TypeError; }\n\
           var dup = new Proxy({}, { ownKeys() { return ['a', 'a']; } });\n\
           var ok2 = false; try { Reflect.ownKeys(dup); } catch (e) { ok2 = e instanceof TypeError; }\n\
           var okk = new Proxy({ m: 1, n: 2 }, { ownKeys(tt) { return Reflect.ownKeys(tt).reverse(); } });\n\
           console.log(ok1, ok2, Reflect.ownKeys(okk).join(','));"),
        m("proxy-set-invariant-and-return", false, false,
          "var t = {}; Object.defineProperty(t, 'x', { value: 1, writable: false, configurable: false });\n\
           var p = new Proxy(t, { set() { return true; } });\n\
           var ok = false; try { 'use strict'; (function () { 'use strict'; p.x = 9; })(); } catch (e) { ok = e instanceof TypeError; }\n\
           var falsy = new Proxy({}, { set() { return false; } });\n\
           var ok2 = false; try { (function () { 'use strict'; falsy.y = 1; })(); } catch (e) { ok2 = e instanceof TypeError; }\n\
           console.log(ok, ok2, Reflect.set(falsy, 'z', 1));"),
        m("proxy-delete-define-invariants", false, false,
          "var t = {}; Object.defineProperty(t, 'x', { value: 1, configurable: false });\n\
           var p = new Proxy(t, { deleteProperty() { return true; } });\n\
           var ok = false; try { delete p.x; } catch (e) { ok = e instanceof TypeError; }\n\
           var ne = Object.preventExtensions({}); var pne = new Proxy(ne, { defineProperty() { return true; } });\n\
           var ok2 = false; try { Object.defineProperty(pne, 'q', { value: 1 }); } catch (e) { ok2 = e instanceof TypeError; }\n\
           console.log(ok, ok2, Reflect.deleteProperty(new Proxy({ a: 1 }, {}), 'a'));"),
        m("proxy-revoked-throws-everywhere", false, false,
          "var r = Proxy.revocable({ x: 1 }, {});\n\
           var before = r.proxy.x;\n\
           r.revoke();\n\
           var res = [];\n\
           function chk(f) { try { f(); res.push('ok'); } catch (e) { res.push(e instanceof TypeError); } }\n\
           chk(function () { return r.proxy.x; });\n\
           chk(function () { r.proxy.x = 1; });\n\
           chk(function () { return 'x' in r.proxy; });\n\
           chk(function () { delete r.proxy.x; });\n\
           chk(function () { Object.keys(r.proxy); });\n\
           chk(function () { Object.getPrototypeOf(r.proxy); });\n\
           chk(function () { Object.isExtensible(r.proxy); });\n\
           console.log(before, res.join(','), r.revoke(), typeof r.proxy, typeof r.revoke);"),
        m("proxy-of-proxy-and-as-prototype", false, false,
          "var t = { v: 1 };\n\
           var inner = new Proxy(t, { get(tt, k) { return (tt[k] || 0) + 10; } });\n\
           var outer = new Proxy(inner, { get(tt, k) { return tt[k] + 100; } });\n\
           var log = [];\n\
           var proto = new Proxy({}, {\n\
             get(tt, k) { log.push('g:' + String(k)); return k === 'foo' ? 42 : undefined; },\n\
             has(tt, k) { log.push('h:' + String(k)); return k === 'foo'; }\n\
           });\n\
           var obj = Object.create(proto); obj.own = 1;\n\
           console.log(outer.v, obj.foo, obj.own, ('foo' in obj), ('own' in obj), ('bar' in obj), log.join('|'));"),
        m("proxy-call-construct-traps", false, false,
          "function target(a, b) { return a + b; }\n\
           var log = [];\n\
           var p = new Proxy(target, {\n\
             apply(f, thisArg, args) { log.push('apply:' + args.join(',')); return f.apply(thisArg, args) * 2; },\n\
             construct(f, args, nt) { log.push('construct:' + args.join(',')); return { sum: args[0] + args[1] }; }\n\
           });\n\
           var okc = false; var bad = new Proxy(function () {}, { construct() { return 5; } });\n\
           try { new bad(); } catch (e) { okc = e instanceof TypeError; }\n\
           console.log(p(2, 3), new p(4, 5).sum, typeof p, p.length, p.name, okc,\n\
           Reflect.apply(p, null, [10, 20]), log.join('|'));"),
        m("proxy-ctor-errors-and-toString", false, false,
          "var errs = [];\n\
           function ce(f) { try { f(); errs.push('ok'); } catch (e) { errs.push(e instanceof TypeError); } }\n\
           ce(function () { new Proxy(1, {}); });\n\
           ce(function () { new Proxy({}, 1); });\n\
           ce(function () { Proxy({}, {}); });\n\
           var pa = new Proxy([1, 2], {});\n\
           var pf = new Proxy(function () {}, {});\n\
           console.log(errs.join(','), Array.isArray(pa), Array.isArray(pf),\n\
           Object.prototype.toString.call(pa), Object.prototype.toString.call(pf),\n\
           Object.prototype.toString.call(new Proxy({}, {})),\n\
           typeof Proxy.revocable, Object.getOwnPropertyDescriptor(Proxy, 'prototype'));"),
        m("proxy-revoked-newtarget-getfunctionrealm", false, false,
          "var handle = Proxy.revocable(function () {}, { get: function () { handle.revoke(); } });\n\
           var f = handle.proxy;\n\
           var t = typeof f;\n\
           var ok = false; try { new f(); } catch (e) { ok = e instanceof TypeError; }\n\
           var h2 = Proxy.revocable(function () {}, {}); var nt = h2.proxy; h2.revoke();\n\
           var ok2 = false; try { Reflect.construct(function () {}, [], nt); } catch (e) { ok2 = e instanceof TypeError; }\n\
           console.log(t, ok, ok2);"),
        m("proxy-prototype-extensibility-traps", false, false,
          "var log = [];\n\
           var t = {};\n\
           var p = new Proxy(t, {\n\
             getPrototypeOf(tt) { log.push('gpo'); return Reflect.getPrototypeOf(tt); },\n\
             setPrototypeOf(tt, v) { log.push('spo'); return Reflect.setPrototypeOf(tt, v); },\n\
             isExtensible(tt) { log.push('ext'); return Reflect.isExtensible(tt); },\n\
             preventExtensions(tt) { log.push('prev'); return Reflect.preventExtensions(tt); }\n\
           });\n\
           var proto = { m() { return 7; } };\n\
           Object.setPrototypeOf(p, proto);\n\
           var e1 = Object.isExtensible(p);\n\
           Object.preventExtensions(p);\n\
           console.log(Object.getPrototypeOf(p) === proto, p.m(), e1, Object.isExtensible(p), log.join('|'));"),
        // ---- S1e: built-in iterator objects ---------------------------
        m("array-iterator-values-keys-entries", false, false,
          "var a = ['x', 'y'];\n\
           var v = a.values(); var r0 = v.next();\n\
           console.log(r0, v.next(), v.next(), v.next(),\n\
             [...a.keys()], [...a.entries()]);"),
        m("array-iterator-identity-tag", false, false,
          "var it = [1, 2][Symbol.iterator]();\n\
           console.log(Array.prototype[Symbol.iterator] === Array.prototype.values,\n\
             typeof it.next, it[Symbol.iterator]() === it,\n\
             Object.prototype.toString.call(it),\n\
             Object.getPrototypeOf(Object.getPrototypeOf(it)) === Object.getPrototypeOf([][Symbol.iterator]()),\n\
             it, Object.keys(it), Object.getOwnPropertyNames(it));"),
        m("array-iterator-live-length", false, false,
          "var a = [1, 2, 3]; var it = a.values();\n\
           var out = []; out.push(it.next().value); a.length = 1;\n\
           out.push(it.next().done); a.push(9, 8);\n\
           console.log(out, [...a.entries()]);"),
        m("array-iterator-for-of-spread", false, false,
          "var a = [10, 20, 30];\n\
           var acc = []; for (var e of a.entries()) acc.push(e);\n\
           function f() { return arguments; }\n\
           console.log(acc, [...a.keys()], Array.from(a.values()),\n\
             [...f(1, 2, 3)[Symbol.iterator]()]);"),
        m("array-iterator-holes-and-getters", false, false,
          "var a = [1, , 3];\n\
           console.log([...a.values()], [...a.keys()]);\n\
           var b = []; Object.defineProperty(b, '0', { get: function () { return 'g'; }, enumerable: true, configurable: true });\n\
           b.length = 1;\n\
           console.log([...b.values()]);"),
        m("string-iterator-codepoints", false, false,
          "var s = 'a\\u{1f600}b';\n\
           var it = s[Symbol.iterator]();\n\
           console.log([...s], it.next(), it.next(),\n\
             typeof it.next, Object.prototype.toString.call(it),\n\
             String.prototype[Symbol.iterator].name);"),
        m("string-iterator-surrogates", false, false,
          "console.log([...'\\ud83d\\ude00'], [...'\\ud800'], [...'ab\\ud83d'],\n\
             'x\\u{1f4a9}y'[Symbol.iterator]().next().value);"),
        m("map-iterator-live-mutation", false, false,
          "var m = new Map([['a', 1], ['b', 2]]);\n\
           var it = m.entries();\n\
           var out = [it.next().value];\n\
           m.delete('b'); m.set('c', 3);\n\
           out.push(it.next().value); out.push(it.next().done);\n\
           console.log(out, [...m.keys()], [...m.values()],\n\
             Object.prototype.toString.call(it));"),
        m("map-set-iterator-tag-identity", false, false,
          "var mi = new Map().keys(); var si = new Set().values();\n\
           console.log(Object.prototype.toString.call(mi), Object.prototype.toString.call(si),\n\
             Set.prototype.keys === Set.prototype.values,\n\
             Set.prototype[Symbol.iterator] === Set.prototype.values,\n\
             Map.prototype[Symbol.iterator] === Map.prototype.entries,\n\
             mi[Symbol.iterator]() === mi, mi, si);"),
        m("set-iterator-entries", false, false,
          "var s = new Set([1, 2, 3]);\n\
           console.log([...s.entries()], [...s.keys()], [...s.values()],\n\
             s.values().next());"),
        m("iterator-next-after-done", false, false,
          "var it = [1][Symbol.iterator]();\n\
           it.next(); var d1 = it.next(); var d2 = it.next();\n\
           console.log(d1, d2, d1.done === true && d2.value === undefined);\n\
           var mit = new Map([['k', 9]]).values(); mit.next();\n\
           console.log(mit.next(), mit.next());"),
        m("iterator-brand-typeerror", false, false,
          "var t = []; var an = Array.prototype.values.call([5]).next;\n\
           try { an.call({}); } catch (e) { t.push(e instanceof TypeError); }\n\
           var mn = new Map().keys().next;\n\
           try { mn.call([1][Symbol.iterator]()); } catch (e) { t.push(e instanceof TypeError); }\n\
           console.log(t);"),
        m("typedarray-iterator", false, false,
          "var a = new Uint8Array([5, 6, 7]);\n\
           console.log([...a.values()], [...a.keys()], [...a.entries()],\n\
             a[Symbol.iterator]().next(),\n\
             Object.prototype.toString.call(a.values()),\n\
             Object.getPrototypeOf(a.values()) === Object.getPrototypeOf([].values()));"),
        m("iterator-early-close-noop", false, false,
          "var out = [];\n\
           for (var x of [1, 2, 3, 4].values()) { if (x === 3) break; out.push(x); }\n\
           var it = [10, 20, 30].values(); var r = it.next().value;\n\
           for (var y of it) { out.push(y); if (y === 20) break; }\n\
           var [a] = [7, 8, 9].values(); var [b, c] = new Set([1, 2, 3]).values();\n\
           console.log(out, r, a, b, c,\n\
             typeof [].values().return, 'return' in [].values());"),
        m("iterator-map-early-close", false, false,
          "var m = new Map([['a', 1], ['b', 2], ['c', 3]]); var seen = [];\n\
           for (var e of m.entries()) { seen.push(e[0]); if (e[0] === 'b') break; }\n\
           var [first] = m.keys();\n\
           console.log(seen, first, typeof new Set([1]).values().return);"),
        m("patched-array-iterator-next-observed", false, false,
          "var AIP = Object.getPrototypeOf([].values());\n\
           var values = [1, 2, 3, 4]; var orig = AIP.next;\n\
           AIP.next = function () { var done = values.length === 0; var value = values.pop(); return { value: value, done: done }; };\n\
           var spread = [...[0]];\n\
           values = [5, 6]; var fromA = Array.from([9, 9, 9]);\n\
           values = [7, 8, 9]; var ta = new Uint8Array([0]);\n\
           values = [1, 2]; var taFrom = Uint8Array.from([0, 0, 0]);\n\
           AIP.next = orig;\n\
           var restored = [...[10, 20]];\n\
           console.log(spread, fromA, [ta.length, ta[0], ta[3]], [taFrom.length, taFrom[0]], restored);"),
        m("patched-array-iterator-next-for-of", false, false,
          // Restore `next` before console.log: a still-patched next would
          // hijack the driver's OWN for-of over its intrinsic-proto table
          // (a driver artifact), so restore first, then project.
          "var AIP = Object.getPrototypeOf([].values());\n\
           var vals = ['a', 'b']; var orig = AIP.next;\n\
           AIP.next = function () { return vals.length ? { value: vals.shift(), done: false } : { value: undefined, done: true }; };\n\
           var out = []; for (var x of [0, 0, 0, 0]) out.push(x);\n\
           AIP.next = orig;\n\
           console.log(out, out.length);"),
        m("array-iterator-manual-protocol", false, false,
          "var a = [1, 2]; var it = a[Symbol.iterator]();\n\
           var res = [];\n\
           var step; while (!(step = it.next()).done) res.push(step.value);\n\
           res.push(it.next().done);\n\
           console.log(res, JSON.stringify([...a.entries()]));"),
        // ---- unresolved identifier ↔ genuine ReferenceError -----------
        // A name in NO environment record and absent from the realm-global
        // registry is an UNRESOLVABLE reference: a bare read throws the exact
        // ReferenceError (uncaught here → Throw completion, ctor/name matched).
        m("undeclared-read-referenceerror", false, false, "unresolvableReference;"),
        m("undeclared-read-uncaught-after-log", false, false,
          "console.log('before'); thisNameDoesNotExist;"),
        // `typeof` of an unresolvable reference is the string "undefined" — no
        // throw — while `typeof` of a MODELED value is its type.
        m("typeof-undeclared-is-undefined", false, false,
          "console.log(typeof thisNameDoesNotExist, typeof alsoNotDeclared, typeof globalThis);"),
        // A caught genuine ReferenceError: identity is exact (instanceof).
        m("caught-referenceerror-instanceof", false, false,
          "var t = false; try { neverDeclaredName; } catch (e) { t = e instanceof ReferenceError; }\n\
           console.log(t);"),
        // Sloppy `delete` of an unresolvable reference evaluates to `true`.
        m("delete-undeclared-is-true", false, false,
          "console.log(delete unresolvableReference, delete anotherUndeclared);"),
        // Strict assignment to an unresolvable reference throws ReferenceError
        // (uncaught here); caught, its identity is exact.
        m("strict-assign-undeclared-referenceerror", false, true,
          "undeclaredAssignTarget = 5;"),
        m("strict-assign-undeclared-caught", false, true,
          "var t = false; try { undeclaredAssignTarget = 5; } catch (e) { t = e instanceof ReferenceError; }\n\
           console.log(t);"),
        // A genuine ReferenceError still fires with an operand around it:
        // `x + 1` resolves `x` first (unresolvable) before the addition.
        m("undeclared-in-binary-referenceerror", false, false,
          "var t = false; try { var q = notThere + 1; } catch (e) { t = e instanceof ReferenceError; }\n\
           console.log(t);"),
        // ---- §26.1 WeakRef ---------------------------------------------
        m("weakref-basics", false, false,
          "var te = function (f) { try { f(); return 'ok'; } catch (e) { return e.constructor.name; } };\n\
           var o = {}; var w = new WeakRef(o);\n\
           console.log(typeof WeakRef, WeakRef.name, WeakRef.length,\n\
           w.deref() === o, Object.prototype.toString.call(w),\n\
           Object.getPrototypeOf(w) === WeakRef.prototype, w,\n\
           te(function () { new WeakRef(5); }), te(function () { WeakRef({}); }),\n\
           te(function () { new WeakRef(Symbol()); }), te(function () { new WeakRef(Symbol.for('k')); }),\n\
           te(function () { WeakRef.prototype.deref.call({}); }));"),
        // ---- §26.2 FinalizationRegistry --------------------------------
        m("finalization-registry", false, false,
          "var te = function (f) { try { f(); return 'ok'; } catch (e) { return e.constructor.name; } };\n\
           var fr = new FinalizationRegistry(function () {});\n\
           var o = {}; var tok = {};\n\
           console.log(typeof FinalizationRegistry, FinalizationRegistry.name, FinalizationRegistry.length,\n\
           Object.prototype.toString.call(fr), Object.getPrototypeOf(fr) === FinalizationRegistry.prototype,\n\
           fr.register(o, 'held', tok), fr.unregister(tok), fr.unregister({}), fr,\n\
           te(function () { new FinalizationRegistry(5); }),\n\
           te(function () { fr.register(o, o); }),\n\
           te(function () { fr.register(5, 1); }));"),
        // ---- §27.1 Iterator (abstract global) --------------------------
        m("iterator-abstract-ctor", false, false,
          "var te = function (f) { try { f(); return 'ok'; } catch (e) { return e.constructor.name; } };\n\
           console.log(typeof Iterator, Iterator.name, Iterator.length,\n\
           Iterator.prototype === Object.getPrototypeOf(Object.getPrototypeOf([].values())),\n\
           Iterator.prototype.constructor === Iterator, Iterator.prototype[Symbol.toStringTag],\n\
           Object.prototype.toString.call(Object.create(Iterator.prototype)),\n\
           te(function () { new Iterator(); }), te(function () { Iterator(); }));"),
        m("iterator-subclass", false, false,
          "class Nums extends Iterator { constructor() { super(); this.i = 0; }\n\
           next() { return this.i < 3 ? { value: this.i++, done: false } : { value: undefined, done: true }; } }\n\
           var acc = []; for (var v of new Nums()) acc.push(v);\n\
           var it = new Nums();\n\
           console.log(acc, it instanceof Iterator, it instanceof Nums,\n\
           Object.getPrototypeOf(Nums.prototype) === Iterator.prototype);"),
        // ---- class static initialization blocks ------------------------
        m("class-static-block", false, false,
          "var log = [];\n\
           class C { static x = 1; static { log.push('A'); log.push(this === C); log.push(this.x); this.y = 2; }\n\
           static z = 3; static { log.push('B'); log.push(this.z); log.push(this.y); } }\n\
           class D { static #p = 5; static { D.pp = D.#p; } static getP() { return D.#p; } }\n\
           console.log(log, C.x, C.y, C.z, D.pp, D.getP());"),
        // ---- for-in over intrinsic namespace objects (empty surface) ---
        m("for-in-intrinsics-empty", false, false,
          "var keys = function (o) { var a = []; for (var k in o) a.push(k); return a; };\n\
           var custom = { a: 1 }; Object.setPrototypeOf(custom, Math);\n\
           console.log(keys(Math), keys(JSON), keys(Reflect), keys(BigInt.prototype),\n\
           keys(WeakRef.prototype), keys(Iterator.prototype), keys(custom));"),
        // ---- §27.1.4 Iterator Helper methods ---------------------------
        m("iter-helper-lazy-adapters", false, false,
          "console.log([1,2,3,4,5].values().map(x=>x*2).toArray());\n\
           console.log([1,2,3,4,5].values().filter(x=>x%2===1).toArray());\n\
           console.log([1,2,3,4,5].values().take(2).toArray());\n\
           console.log([1,2,3,4,5].values().drop(2).toArray());\n\
           console.log([1,2,3].values().map((x,i)=>x+':'+i).toArray());\n\
           console.log([10,20,30].values().filter((x,i)=>i>0).toArray());\n\
           console.log([1,2,3,4,5,6].values().map(x=>x*10).filter(x=>x>20).take(2).toArray());"),
        m("iter-helper-eager-consumers", false, false,
          "console.log([1,2,3,4].values().reduce((a,b)=>a+b,0), [1,2,3,4].values().reduce((a,b)=>a+b));\n\
           console.log([1,2,3].values().some(x=>x>2), [1,2,3].values().every(x=>x>0), [1,2,3].values().find(x=>x>1));\n\
           console.log([1,2,3].values().some(x=>x>9), [1,2,3].values().every(x=>x>1), [1,2,3].values().find(x=>x>9));\n\
           var acc=[]; [5,6,7].values().forEach((x,i)=>acc.push(x*100+i)); console.log(acc);\n\
           var e=false; try{ [].values().reduce((a,b)=>a+b); }catch(err){ e=err instanceof TypeError; } console.log(e);"),
        m("iter-helper-flatmap", false, false,
          "console.log([1,2,3].values().flatMap(x=>[x,x*10]).toArray());\n\
           console.log([10,20].values().flatMap((x,i)=>[x,i]).toArray());\n\
           console.log([1,2].values().flatMap(x=>[]).toArray());\n\
           var e=false; try{ [1].values().flatMap(x=>x).toArray(); }catch(err){ e=err instanceof TypeError; } console.log(e);\n\
           var e2=false; try{ [1].values().flatMap(x=>'ab').toArray(); }catch(err){ e2=err instanceof TypeError; } console.log(e2);"),
        m("iter-helper-return-close", false, false,
          "var log=[]; var it=[1,2,3][Symbol.iterator](); it.return=function(){log.push('R'); return {done:true};};\n\
           var h=it.map(x=>x*2);\n\
           log.push(JSON.stringify(h.next()));\n\
           log.push(JSON.stringify(h.return()));\n\
           log.push(JSON.stringify(h.next()));\n\
           console.log(log);"),
        m("iter-helper-take-drop-rangeerror", false, false,
          "function mk(){return [1,2,3].values();}\n\
           var r=[];\n\
           try{ mk().take(NaN); }catch(e){ r.push(e.constructor.name); }\n\
           try{ mk().take(-1); }catch(e){ r.push(e.constructor.name); }\n\
           try{ mk().drop(-5); }catch(e){ r.push(e.constructor.name); }\n\
           r.push(mk().take(Infinity).take(2).toArray().join(','));\n\
           console.log(r);"),
        m("iter-helper-brand-and-tag", false, false,
          "var h=[1].values().map(x=>x);\n\
           console.log(Object.prototype.toString.call(h), h[Symbol.toStringTag],\n\
           Object.getPrototypeOf(Object.getPrototypeOf(h))===Iterator.prototype);\n\
           var r=[];\n\
           try{ Iterator.prototype.map.call(5,x=>x); }catch(e){ r.push(e.constructor.name); }\n\
           try{ Iterator.prototype.map.call([1].values(),'nope'); }catch(e){ r.push(e.constructor.name); }\n\
           try{ Iterator.prototype.reduce.call([1].values(),'nope'); }catch(e){ r.push(e.constructor.name); }\n\
           try{ Iterator.prototype.take.call(5,1); }catch(e){ r.push(e.constructor.name); }\n\
           console.log(r);"),
        m("iter-helper-over-generator", false, false,
          "function* g(){ yield 1; yield 2; yield 3; yield 4; }\n\
           console.log(g().map(x=>x*x).toArray());\n\
           console.log(g().filter(x=>x%2===0).toArray());\n\
           console.log(g().take(2).toArray());\n\
           console.log(g().drop(1).flatMap(x=>[x,-x]).toArray());\n\
           console.log(g().reduce((a,b)=>a+b));"),
        m("iter-helper-flatmap-return-closes", false, false,
          "function tracked(name, vals, log){ var i=0; return { name:name, [Symbol.iterator](){ return this; },\n\
             next(){ return i<vals.length?{value:vals[i++],done:false}:{done:true}; },\n\
             return(){ log.push(name+':return'); return {}; } }; }\n\
           var log=[];\n\
           var outer = tracked('OUTER',[1,2,3],log); Object.setPrototypeOf(outer, Iterator.prototype);\n\
           var h = outer.flatMap(function(x){ return [x*10, x*100]; });\n\
           log.push('n1:'+JSON.stringify(h.next()));\n\
           log.push('ret:'+JSON.stringify(h.return()));\n\
           log.push('n2:'+JSON.stringify(h.next()));\n\
           console.log(log);\n\
           var log2=[];\n\
           var inner = tracked('INNER',[7,8],log2);\n\
           var outer2 = tracked('OUTER',[1,2],log2); Object.setPrototypeOf(outer2, Iterator.prototype);\n\
           var h2 = outer2.flatMap(function(x){ return inner; });\n\
           log2.push('n1:'+JSON.stringify(h2.next()));\n\
           log2.push('ret:'+JSON.stringify(h2.return()));\n\
           console.log(log2);"),
        m("iter-helper-arg-failure-closes", false, false,
          "function mk(){ return { closed:false, __proto__:Iterator.prototype,\n\
             get next(){ throw new Error('next read'); }, return(){ this.closed=true; return {}; } }; }\n\
           var log=[];\n\
           function chk(label, fn){ var c=mk(); var name='ok'; try{ fn(c); }catch(e){ name=e.constructor.name; }\n\
             log.push(label+':'+name+':'+c.closed); }\n\
           chk('map', function(c){ return c.map('x'); });\n\
           chk('take-nan', function(c){ return c.take(NaN); });\n\
           chk('take-neg', function(c){ return c.take(-1); });\n\
           chk('drop-neg', function(c){ return c.drop(-3); });\n\
           chk('reduce', function(c){ return c.reduce('x'); });\n\
           chk('some', function(c){ return c.some('x'); });\n\
           console.log(log);"),
        m("iter-helper-method-shape", false, false,
          "var d=Object.getOwnPropertyDescriptor(Iterator.prototype,'map');\n\
           console.log(d.writable, d.enumerable, d.configurable, typeof d.value);\n\
           console.log(Iterator.prototype.toArray.length, Iterator.prototype.map.length,\n\
           Iterator.prototype.map.name, Iterator.prototype.reduce.name,\n\
           Iterator.prototype.flatMap.length, Iterator.prototype.find.name);"),
    ]
}

#[test]
fn embedded_mini_cases_vs_node() {
    let Some(env) = env_or_skip("embedded_mini_cases_vs_node") else {
        return;
    };
    let assert_path = env.corpus.join("harness/assert.js");
    let sta_path = env.corpus.join("harness/sta.js");
    let assert_src = std::fs::read_to_string(&assert_path).expect("read assert.js");
    let sta_src = std::fs::read_to_string(&sta_path).expect("read sta.js");

    let cases = mini_cases();
    assert!(cases.len() >= 30, "mini-case count contract");
    let mut failures: Vec<String> = Vec::new();
    for case in &cases {
        let includes_src: Vec<&str> = if case.with_harness {
            vec![assert_src.as_str(), sta_src.as_str()]
        } else {
            Vec::new()
        };
        let mine = match evaluate_case(&includes_src, case.body, case.strict) {
            InterpOutcome::Trace(t) => t,
            InterpOutcome::NoCoverage { reason } => {
                failures.push(format!("{}: NoCoverage: {reason}", case.name));
                continue;
            }
        };
        let include_paths: Vec<PathBuf> = if case.with_harness {
            vec![assert_path.clone(), sta_path.clone()]
        } else {
            Vec::new()
        };
        match node_trace(&env, case.name, &include_paths, case.body, case.strict) {
            Ok(node) => {
                if !traces_equal(&mine, &node) {
                    failures.push(format!(
                        "{}: DIVERGENCE: {}",
                        case.name,
                        explain_divergence(&mine, &node).unwrap_or_else(|| "unlocalized".to_string())
                    ));
                }
            }
            Err(e) => failures.push(format!("{}: node: {e}", case.name)),
        }
    }
    assert!(
        failures.is_empty(),
        "embedded differential failures:\n{}",
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// (a1a) String.prototype.matchAll / RegExp.prototype[@@matchAll] →
// %RegExpStringIterator% (22.2.9). Every case is mandated COVERED and
// trace-equal to Node, and Node==Bun is asserted as a guard (matchAll is
// engine-stable). Probes the empty-match global advance (deferred to the
// post-yield resume), fullUnicode surrogate advance, named/numeric captures,
// the non-global-RegExp TypeError, string-argument /g coercion, the iterator
// protocol (self-iterable, done latching, @@toStringTag), and lastIndex
// independence of the cloned matcher.
// ---------------------------------------------------------------------------
const MATCHALL_EXACT_CASES: &[(&str, &str)] = &[
    ("basic-captures",
     "console.log(JSON.stringify([...'a1b2c3'.matchAll(/([a-z])(\\d)/g)]));"),
    ("tostringtag",
     "console.log(Object.prototype.toString.call('a'.matchAll(/a/g)));"),
    ("self-iterable",
     "var it = 'aa'.matchAll(/a/g); console.log(it[Symbol.iterator]() === it);"),
    ("match-indices",
     "console.log([...'xax'.matchAll(/x/g)].map(function(m){return m.index;}).join(','));"),
    ("empty-match-advance",
     "console.log(JSON.stringify([...'abc'.matchAll(/x*/g)].map(function(m){return [m[0], m.index];})));"),
    ("non-global-regexp-typeerror",
     "var t=false; try { 'abc'.matchAll(/a/); } catch(e){ t = e instanceof TypeError; } console.log(t);"),
    ("string-arg-coerces-global",
     "console.log(JSON.stringify([...'a.b.c'.matchAll('.')].map(function(m){return [m[0], m.index];})));"),
    ("named-groups",
     "console.log(JSON.stringify([...'2024-01'.matchAll(/(?<y>\\d{4})-(?<m>\\d{2})/g)].map(function(m){return { y: m.groups.y, mo: m.groups.m };})));"),
    ("fullunicode-empty-advance",
     "console.log(JSON.stringify([...'\\u{1F600}x'.matchAll(/(?:)/gu)].map(function(m){return m.index;})));"),
    ("iterator-done-latches",
     "var it='a'.matchAll(/a/g); console.log(JSON.stringify(it.next().value[0]), JSON.stringify(it.next()), JSON.stringify(it.next()));"),
    ("this-null-typeerror",
     "var t=false; try { String.prototype.matchAll.call(null, /a/g); } catch(e){ t = e instanceof TypeError; } console.log(t);"),
    ("no-matches-empty",
     "console.log([...'abc'.matchAll(/z/g)].length);"),
    ("lastindex-independent",
     "var r=/a/g; r.lastIndex=99; var it='aaa'.matchAll(r); var out=[...it].map(function(m){return m.index;}); console.log(out.join(','), r.lastIndex);"),
    ("regexp-symbol-matchall-direct",
     "console.log([...(/b/g)[Symbol.matchAll]('abcb')].map(function(m){return m.index;}).join(','));"),
    ("overlapping-caps-undefined",
     "console.log(JSON.stringify([...'ac'.matchAll(/a(b)?/g)].map(function(m){return m[1] === undefined ? 'u' : m[1];})));"),
];

#[test]
fn matchall_regexp_string_iterator_exact() {
    let Some(env) = env_or_skip("matchall_regexp_string_iterator_exact") else {
        return;
    };
    let mut failures: Vec<String> = Vec::new();
    for (name, body) in MATCHALL_EXACT_CASES {
        let mine = match evaluate_case(&[], body, false) {
            InterpOutcome::Trace(t) => t,
            InterpOutcome::NoCoverage { reason } => {
                failures.push(format!("{name}: NoCoverage (must be covered): {reason}"));
                continue;
            }
        };
        let node = match node_trace(&env, name, &[], body, false) {
            Ok(t) => t,
            Err(e) => {
                failures.push(format!("{name}: node: {e}"));
                continue;
            }
        };
        if !traces_equal(&mine, &node) {
            failures.push(format!(
                "{name}: interp!=node: {}",
                explain_divergence(&mine, &node).unwrap_or_else(|| "unlocalized".to_string())
            ));
        }
        // Node==Bun guard (matchAll is engine-stable).
        if let Some(bun) = &env.bun {
            match engine_trace(&env, bun, name, &[], body, false) {
                Ok(b) => {
                    if !traces_equal(&node, &b) {
                        failures.push(format!("{name}: node!=bun (unexpected for matchAll)"));
                    }
                }
                Err(e) => failures.push(format!("{name}: bun: {e}")),
            }
        }
    }
    assert!(
        failures.is_empty(),
        "matchAll differential failures:\n{}",
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// (a1a2) for-in over the fully-modeled iterator / generator / promise /
// async-function intrinsic prototypes: their enumerable own surface is empty,
// so for-in must yield ONLY the instance's own + inherited enumerable string
// keys (never refuse). Calibrated exact vs Node and Bun.
// ---------------------------------------------------------------------------
const FORIN_INTRINSIC_CASES: &[(&str, &str)] = &[
    ("array-iterator-empty",
     "var o=[]; for (var k in [1,2].values()) o.push(k); console.log(JSON.stringify(o));"),
    ("map-iterator-empty",
     "var o=[]; for (var k in new Map([[1,2]]).entries()) o.push(k); console.log(JSON.stringify(o));"),
    ("string-iterator-empty",
     "var o=[]; for (var k in 'ab'[Symbol.iterator]()) o.push(k); console.log(JSON.stringify(o));"),
    ("generator-instance-empty",
     "function* g(){ yield 1; } var o=[]; for (var k in g()) o.push(k); console.log(JSON.stringify(o));"),
    ("promise-instance-empty",
     "var o=[]; for (var k in Promise.resolve(1)) o.push(k); console.log(JSON.stringify(o));"),
    ("generator-function-empty",
     "function* g(){} var o=[]; for (var k in g) o.push(k); console.log(JSON.stringify(o));"),
    ("async-function-empty",
     "async function af(){} var o=[]; for (var k in af) o.push(k); console.log(JSON.stringify(o));"),
    ("matchall-iterator-empty",
     "var o=[]; for (var k in 'aa'.matchAll(/a/g)) o.push(k); console.log(JSON.stringify(o));"),
    ("iterator-own-enumerable",
     "var it=[1].values(); it.foo=7; it.bar=8; var o=[]; for (var k in it) o.push(k); console.log(JSON.stringify(o));"),
    ("iterator-inherited-enumerable",
     "Object.prototype.INH=1; var o=[]; for (var k in [1].values()) o.push(k); delete Object.prototype.INH; console.log(JSON.stringify(o));"),
    ("generator-function-own",
     "function* g(){} g.z=1; var o=[]; for (var k in g) o.push(k); console.log(JSON.stringify(o));"),
];

#[test]
fn for_in_intrinsic_instances_exact() {
    let Some(env) = env_or_skip("for_in_intrinsic_instances_exact") else {
        return;
    };
    let mut failures: Vec<String> = Vec::new();
    for (name, body) in FORIN_INTRINSIC_CASES {
        let mine = match evaluate_case(&[], body, false) {
            InterpOutcome::Trace(t) => t,
            InterpOutcome::NoCoverage { reason } => {
                failures.push(format!("{name}: NoCoverage (must be covered): {reason}"));
                continue;
            }
        };
        let node = match node_trace(&env, name, &[], body, false) {
            Ok(t) => t,
            Err(e) => {
                failures.push(format!("{name}: node: {e}"));
                continue;
            }
        };
        if !traces_equal(&mine, &node) {
            failures.push(format!(
                "{name}: interp!=node: {}",
                explain_divergence(&mine, &node).unwrap_or_else(|| "unlocalized".to_string())
            ));
        }
        if let Some(bun) = &env.bun {
            match engine_trace(&env, bun, name, &[], body, false) {
                Ok(b) => {
                    if !traces_equal(&node, &b) {
                        failures.push(format!("{name}: node!=bun (unexpected)"));
                    }
                }
                Err(e) => failures.push(format!("{name}: bun: {e}")),
            }
        }
    }
    assert!(
        failures.is_empty(),
        "for-in intrinsic-instance differential failures:\n{}",
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// (a1b) S1f adversarial eval / Function-constructor / sloppy-mode cases: the
// PerformEval + EvalDeclarationInstantiation + CreateDynamicFunction web,
// probed at the corners the corpus sample does not densely hit. Each is
// mandated COVERED and trace-equal to Node, or to Bun under the either-engine
// rule (eval/Function are engine-stable, but the harness keeps the fallback).
// ---------------------------------------------------------------------------

/// (name, with_harness, mandate_exact, body). All run in bare (sloppy) mode
/// unless the body carries its own prologue. `mandate_exact = false` still
/// forbids a WRONG trace; it only tolerates a sound NoCoverage refusal — used
/// for cases that PROVE a name did not leak by reading it, which the head
/// soundly refuses (an unresolved read might be a real engine global).
const EVAL_FN_EXACT_CASES: &[(&str, bool, bool, &str)] = &[
    // Direct eval: completion values, var/function hoist into caller scope,
    // reads+writes of caller bindings.
    ("direct-completion", false, true,
     "console.log(eval('1 + 2'), eval('var v = 5; v * 2'), eval('if(true){}'), eval('42;;'), eval('for(;;){break}'));"),
    ("direct-var-hoist-global", false, true,
     "eval('var gv = 9; function gf(){ return 3; }'); console.log(typeof gv, gv, typeof gf, gf());"),
    ("direct-var-hoist-fn", false, true,
     "function f(){ eval('var z = 99;'); return z; } console.log(f());"),
    ("direct-read-write-caller", false, true,
     "function f(){ var a = 1; eval('a = a + 40; var b = a + 1;'); return [a, b]; } console.log(f().join(','));"),
    ("direct-sees-caller-let", false, true,
     "function f(){ let loc = 7; return eval('loc + 1'); } console.log(f());"),
    ("direct-paren-still-direct", false, true,
     "function f(){ let loc = 5; return (eval)('loc * 2'); } console.log(f());"),
    // Strict direct eval: its var/function do NOT leak into the caller
    // (observed by a read the head soundly refuses — refusal-tolerant).
    ("strict-eval-isolation", false, false,
     "function f(){ 'use strict'; eval('var q = 7;'); try { return q; } catch(e){ return e.constructor.name; } } console.log(f());"),
    ("strict-caller-inherits", false, false,
     "'use strict'; function f(){ eval('var q = 1;'); return typeof q === 'undefined'; } console.log(f());"),
    ("eval-prologue-strict", false, true,
     "var t = false; try { eval('\"use strict\"; with(1){}'); } catch(e){ t = e instanceof SyntaxError; } console.log(t);"),
    // Indirect eval: global scope, no local visibility, base non-strict.
    ("indirect-global-scope", false, false,
     "function f(){ var loc = 3; try { return (0,eval)('typeof loc'); } catch(e){ return 'ERR'; } } console.log(f());"),
    ("indirect-var-on-global", false, true,
     "var e = eval; e('var iv = 11;'); console.log(iv, typeof iv);"),
    ("indirect-non-string", false, true,
     "console.log((0,eval)(123), (0,eval)(true), typeof (0,eval)({}));"),
    ("eval-non-string-direct", false, true,
     "console.log(eval(123), eval(null), eval(undefined));"),
    // eval SyntaxError from a genuine parse error.
    ("eval-syntax-error", false, true,
     "var t = false; try { eval('var ='); } catch(e){ t = e instanceof SyntaxError; } console.log(t);"),
    ("eval-return-illegal", false, true,
     "var t = false; try { eval('return 1;'); } catch(e){ t = e instanceof SyntaxError; } console.log(t);"),
    // Delete an eval-created local var (deletable binding).
    ("eval-delete-local-var", false, true,
     "var initial = null; (function(){ eval('initial = x; delete x; var x;'); }()); console.log(initial);"),
    // The Function constructor: name/length/scope, call and construct forms.
    ("function-ctor-basics", false, true,
     "var f = new Function('a', 'b', 'return a + b;'); console.log(f(2, 3), f.name, f.length, f instanceof Function);"),
    ("function-ctor-call-form", false, true,
     "var g = Function('x', 'return x * 2;'); console.log(g(21), g.length, g.name);"),
    ("function-ctor-global-scope", false, false,
     "function o(){ var loc = 9; return new Function('return typeof loc;')(); } console.log(o());"),
    ("function-ctor-empty", false, true,
     "console.log(new Function().name, new Function()(), new Function('return 7;')(), new Function('a,', 'return a;')(5));"),
    ("function-ctor-syntax-error", true, true,
     "assert.throws(SyntaxError, function(){ new Function('/*', '*/'); });\n\
      assert.throws(SyntaxError, function(){ new Function(')', ''); });\n\
      assert.throws(SyntaxError, function(){ new Function('a b', 'return 1'); });\n\
      console.log('ok');"),
    ("function-ctor-is-ctor", false, true,
     "var C = new Function('this.x = 1;'); var i = new C(); console.log(i.x, i instanceof C);"),
    // Sloppy this substitution + assignment-to-undeclared-creates-global.
    ("sloppy-this-primitive", false, true,
     "function f(){ return typeof this; } console.log(f.call(5), f.call('s'), f.call(undefined) === typeof globalThis);"),
    ("sloppy-undeclared-global", false, true,
     "function f(){ undeclaredGlobalX = 42; } f(); console.log(undeclaredGlobalX, typeof undeclaredGlobalX);"),
    // Nested eval; eval inside a function returning a closure over eval-var.
    ("nested-eval", false, true,
     "console.log(eval('eval(\"3 + 4\")'), eval('(0,eval)(\"5 * 5\")'));"),
    ("eval-closure-capture", false, true,
     "function mk(){ eval('var secret = 7;'); return function(){ return secret; }; } console.log(mk()());"),
    // Completion value corners: trailing function decl leaves the prior value;
    // a lone function decl / block is undefined; let/const evaluate.
    ("eval-completion-corners", false, true,
     "console.log(eval('1; function f(){}'), eval('function g(){}'), eval('let a=1; const b=2; a+b'), eval('2; { let c=9; }'));"),
    // Direct eval `this` is the caller's this.
    ("eval-this-direct", false, true,
     "var o = { m: function(){ return eval('this') === o; } }; console.log(o.m());"),
    // Function constructor: default/rest/destructuring params drive length; a
    // strict body directive makes the created function strict.
    ("function-ctor-param-forms", false, true,
     "var ff = new Function('a=5', '...r', 'return [a, r.length];');\n\
      console.log(ff().join(','), ff(1,2,3).join(','), ff.length, ff.name);"),
    ("function-ctor-strict-body", false, true,
     "var sf = new Function('\"use strict\"; return this;'); console.log(sf.call(5), typeof sf.call(undefined));"),
    ("function-ctor-destructuring", false, true,
     "var dd = new Function('{a,b}', 'return a + b;'); console.log(dd({a:1,b:2}), dd.length);"),
    ("eval-throw-propagates", false, true,
     "var caught; try { eval('throw 42;'); } catch(e){ caught = e; } console.log(caught);"),
    // Direct eval resolves the caller's arguments object.
    ("eval-arguments", false, true,
     "function f(a, b){ return eval('arguments[0] + arguments[1]'); }\n\
      function g(){ return eval('arguments.length'); }\n\
      console.log(f(10, 20), g(1, 2, 3));"),
    // eval producing function values (NFE self-binding), parenthesized object/
    // array/template expressions.
    ("eval-expression-values", false, true,
     "console.log(eval('([1,2,3])').length, eval('({a:1}).a'), eval('`t${1+1}`'), eval('(function x(){ return typeof x; })')());"),
    // Function constructor: `return` is not a valid parameter (SyntaxError);
    // length reflects the declared parameter count.
    ("function-ctor-length-and-error", true, true,
     "assert.throws(SyntaxError, function(){ new Function('return', '1'); });\n\
      console.log(new Function('return arguments.length;').length, new Function('a','b','c','return 0;').length);"),
    // An optional call `eval?.(x)` and a spread `eval(...a)` are INDIRECT eval
    // (global scope) — the result still computes, but a caller local is not
    // visible (soundly refused).
    ("eval-optional-and-spread", false, true,
     "console.log(eval?.('1 + 2'), eval(...['4 * 4']));"),
    ("eval-optional-is-indirect", false, false,
     "function f(){ var loc = 7; try { return eval?.('loc'); } catch(e){ return 'ERR:' + e.constructor.name; } } console.log(f());"),
];

#[test]
fn eval_function_adversarial_exact() {
    let Some(env) = env_or_skip("eval_function_adversarial_exact") else {
        return;
    };
    let assert_path = env.corpus.join("harness/assert.js");
    let sta_path = env.corpus.join("harness/sta.js");
    let assert_src = std::fs::read_to_string(&assert_path).expect("read assert.js");
    let sta_src = std::fs::read_to_string(&sta_path).expect("read sta.js");
    let mut failures: Vec<String> = Vec::new();

    for (name, with_harness, mandate_exact, body) in EVAL_FN_EXACT_CASES {
        let includes_src: Vec<&str> = if *with_harness {
            vec![assert_src.as_str(), sta_src.as_str()]
        } else {
            Vec::new()
        };
        let include_paths: Vec<PathBuf> = if *with_harness {
            vec![assert_path.clone(), sta_path.clone()]
        } else {
            Vec::new()
        };
        let mine = match evaluate_case(&includes_src, body, false) {
            InterpOutcome::Trace(t) => t,
            InterpOutcome::NoCoverage { reason } => {
                if *mandate_exact {
                    failures.push(format!("{name}: NoCoverage (exactness mandated): {reason}"));
                } else {
                    eprintln!("{name}: sound refusal (accepted): {reason}");
                }
                continue;
            }
        };
        match node_trace(&env, name, &include_paths, body, false) {
            Ok(node) => {
                if traces_equal(&mine, &node) {
                    continue;
                }
                if let Some(bun) = env.bun.clone() {
                    match engine_trace(&env, &bun, &format!("{name}-bun"), &include_paths, body, false) {
                        Ok(bt) if traces_equal(&mine, &bt) => {}
                        Ok(_) => failures.push(format!(
                            "{name}: WRONG TRACE (both engines): {}",
                            explain_divergence(&mine, &node)
                                .unwrap_or_else(|| "unlocalized".to_string())
                        )),
                        Err(e) => failures.push(format!("{name}: bun: {e}")),
                    }
                } else {
                    failures.push(format!(
                        "{name}: DIVERGENCE: {}",
                        explain_divergence(&mine, &node)
                            .unwrap_or_else(|| "unlocalized".to_string())
                    ));
                }
            }
            Err(e) => failures.push(format!("{name}: node: {e}")),
        }
    }
    assert!(
        failures.is_empty(),
        "eval/Function adversarial cases not exact:\n{}",
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// (a2) Calibration divergence cases (M1 D3, 2026-07-21): the 12 corpus cases
// where the four-head calibration caught the head emitting a wrong trace.
// These must now be EXACT — covered and trace-equal in every mandated mode
// (a refusal here fails: both families are pure-language semantics).
// ---------------------------------------------------------------------------

const CALIBRATION_EXACT_CASES: [&str; 15] = [
    // Family 0: invalid RegExp GroupSpecifier names (2026-07-22 four-head
    // gate): a non-ID_Start group-name start must throw SyntaxError at
    // compile. trust-js-regexp once misrouted `(?<🐕>…)` into a lookbehind
    // because the dog-emoji lead surrogate U+D83D truncates to '=' — so the
    // bad name was accepted and `assert.throws(SyntaxError, …)` failed.
    "test/built-ins/RegExp/named-groups/unicode-property-names-invalid.js",
    "test/built-ins/RegExp/named-groups/non-unicode-property-names-invalid.js",
    // Family 1: function own-property order (`length` before `name`).
    "test/built-ins/Function/property-order.js",
    "test/built-ins/ThrowTypeError/property-order.js",
    // S1b gate divergence (2026-07-21): GetValue-context super property with
    // uninitialized `this` — the this-TDZ check precedes key evaluation
    // (Node and Bun agree; the assignment-flavored contexts diverge between
    // engines and REFUSE instead).
    "test/language/expressions/super/prop-expr-uninitialized-this-getvalue.js",
    // Family 2: ForIn/OfHeadEvaluation TDZ + head/body lexical scoping.
    "test/language/statements/for-in/head-const-bound-names-fordecl-tdz.js",
    "test/language/statements/for-in/head-let-bound-names-fordecl-tdz.js",
    "test/language/statements/for-in/scope-body-lex-open.js",
    "test/language/statements/for-in/scope-head-lex-close.js",
    "test/language/statements/for-in/scope-head-lex-open.js",
    "test/language/statements/for-of/head-const-bound-names-fordecl-tdz.js",
    "test/language/statements/for-of/head-let-bound-names-fordecl-tdz.js",
    "test/language/statements/for-of/scope-body-lex-open.js",
    "test/language/statements/for-of/scope-head-lex-close.js",
    "test/language/statements/for-of/scope-head-lex-open.js",
];

#[test]
fn calibration_divergence_cases_exact() {
    let Some(env) = env_or_skip("calibration_divergence_cases_exact") else {
        return;
    };
    let mut failures: Vec<String> = Vec::new();
    for (ci, rel) in CALIBRATION_EXACT_CASES.iter().enumerate() {
        let body = std::fs::read_to_string(env.corpus.join(rel))
            .unwrap_or_else(|e| panic!("read {rel}: {e}"));
        let fm = parse_fm(&body);
        assert!(fm.includes.is_empty(), "{rel}: unexpected extra includes");
        let modes: &[bool] = if fm.flags.iter().any(|f| f == "onlyStrict") {
            &[true]
        } else if fm.flags.iter().any(|f| f == "noStrict" || f == "raw") {
            &[false]
        } else {
            &[false, true]
        };
        let include_paths = vec![
            env.corpus.join("harness/assert.js"),
            env.corpus.join("harness/sta.js"),
        ];
        let include_srcs: Vec<String> = include_paths
            .iter()
            .map(|p| std::fs::read_to_string(p).expect("read include"))
            .collect();
        let include_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();
        for &strict in modes {
            let mode = if strict { "strict" } else { "bare" };
            let mine = match evaluate_case(&include_refs, &body, strict) {
                InterpOutcome::Trace(t) => t,
                InterpOutcome::NoCoverage { reason } => {
                    failures.push(format!("{rel} [{mode}]: NoCoverage (exactness mandated): {reason}"));
                    continue;
                }
            };
            match node_trace(&env, &format!("calib-{ci}-{mode}"), &include_paths, &body, strict) {
                Ok(node) => {
                    if !traces_equal(&mine, &node) {
                        failures.push(format!(
                            "{rel} [{mode}]: DIVERGENCE: {}",
                            explain_divergence(&mine, &node)
                                .unwrap_or_else(|| "unlocalized".to_string())
                        ));
                    }
                }
                Err(e) => failures.push(format!("{rel} [{mode}]: node: {e}")),
            }
        }
    }
    assert!(
        failures.is_empty(),
        "calibration divergence cases not exact:\n{}",
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// (a3) Typed-array calibration divergence cases (S1f gate, 2026-07-22): the
// three typed-array runs the recorded gate caught the head emitting a WRONG
// trace on, all in the new integer-indexed exotic / %TypedArray% surface.
// Includes are assembled per the run-mode contract (assert.js + sta.js +
// frontmatter includes, e.g. testTypedArray.js), so the constructor-sweep
// harness runs in full.
//
// Policy (THE BAR): ZERO wrong traces — every covered run must be trace-equal
// to Node, or to Bun under the audited either-engine rule. A `mandated_exact`
// case additionally forbids a NoCoverage refusal.
//   1. includes/length-zero-returns-false — the fix makes the head short-
//      circuit (return false) before the poisoned fromIndex coercion, so the
//      constructor sweep now advances past that combo into the `iterable` arg
//      factory (typed-array-from-iterable via Array.prototype[@@iterator]),
//      which is a SEPARATE unimplemented feature: the full file becomes a
//      SOUND REFUSAL, not a wrong trace. The exact step-ordering behavior the
//      bug concerned is pinned mandated-exact by the focused case below.
//   2. with/index-validated-against-current-length — mandated-exact:
//      IsValidIntegerIndex (step 9) is re-checked AFTER ToNumber(value) (step
//      8) against the current (resized) length, while the captured `len` sizes
//      the result array.
//   3. Set/key-is-out-of-bounds-receiver-is-proto — mandated-exact: a typed
//      array reached as a prototype in OrdinarySetWithOwnDescriptor dispatches
//      its exotic [[Set]] (SameValue(O,Receiver) → TypedArraySetElement,
//      ToNumber observable, an out-of-range index discards the write), true.
// ---------------------------------------------------------------------------

/// (rel path, mandated_exact). `mandated_exact=false` still forbids a wrong
/// trace; it only tolerates a sound NoCoverage refusal on an unrelated gap.
const TYPEDARRAY_CALIBRATION_CASES: [(&str, bool); 4] = [
    ("test/built-ins/TypedArray/prototype/includes/length-zero-returns-false.js", false),
    ("test/built-ins/TypedArray/prototype/with/index-validated-against-current-length.js", true),
    (
        "test/built-ins/TypedArrayConstructors/internals/Set/key-is-out-of-bounds-receiver-is-proto.js",
        true,
    ),
    // S1e iterator-objects gate (2026-07-22): `new TypedArray(arrayArg)` must
    // drive the array's @@iterator protocol, honoring a PATCHED
    // %ArrayIteratorPrototype%.next even under a pristine @@iterator. The
    // internal fast-iteration path is now gated on the iterator prototype's
    // `next` still being intrinsic, so this falls to the general protocol and
    // observes the patched `next` (result [4,3,2,1]), mandated exact.
    (
        "test/built-ins/TypedArrayConstructors/ctors/object-arg/iterated-array-with-modified-array-iterator.js",
        true,
    ),
];

/// A focused, fully in-reach case for the includes step-ordering fix itself
/// (length-0 typed array + poisoned fromIndex, across several element types).
/// Mandated-exact vs both engines — this is the direct proof of case 1.
const INCLUDES_LEN_ZERO_FOCUSED: &str = "\
var fromIndex = { valueOf: function () { throw new Test262Error(); } };\n\
[Int8Array, Uint8Array, Uint8ClampedArray, Int16Array, Uint16Array, Int32Array, \
Uint32Array, Float32Array, Float64Array].forEach(function (TA) {\n\
  var sample = new TA(0);\n\
  assert.sameValue(sample.includes(0), false, 'returns false');\n\
  assert.sameValue(sample.includes(), false, 'returns false - no arg');\n\
  assert.sameValue(sample.includes(0, fromIndex), false, 'length before ToInteger');\n\
});\n\
console.log('includes-len-zero-ok');\n";

#[test]
fn typedarray_calibration_cases_exact() {
    let Some(env) = env_or_skip("typedarray_calibration_cases_exact") else {
        return;
    };
    let mut failures: Vec<String> = Vec::new();

    // Helper: compare `mine` against Node, then (either-engine rule) Bun.
    // Returns Err(message) on a wrong trace / engine error, Ok(()) on equal.
    let cmp = |failures: &mut Vec<String>,
                   env: &Env,
                   tag: &str,
                   rel: &str,
                   mode: &str,
                   include_paths: &[PathBuf],
                   body: &str,
                   strict: bool,
                   mine: &ObservableTrace| {
        match node_trace(env, tag, include_paths, body, strict) {
            Ok(node) => {
                if traces_equal(mine, &node) {
                    return;
                }
                if let Some(bun) = env.bun.clone() {
                    match engine_trace(env, &bun, &format!("{tag}-bun"), include_paths, body, strict) {
                        Ok(bt) if traces_equal(mine, &bt) => {}
                        Ok(_) => failures.push(format!(
                            "{rel} [{mode}]: WRONG TRACE (both engines): {}",
                            explain_divergence(mine, &node)
                                .unwrap_or_else(|| "unlocalized".to_string())
                        )),
                        Err(e) => failures.push(format!("{rel} [{mode}]: bun: {e}")),
                    }
                } else {
                    failures.push(format!(
                        "{rel} [{mode}]: WRONG TRACE: {}",
                        explain_divergence(mine, &node).unwrap_or_else(|| "unlocalized".to_string())
                    ));
                }
            }
            Err(e) => failures.push(format!("{rel} [{mode}]: node: {e}")),
        }
    };

    // The three recorded full-file cases: zero wrong traces; `with`/`Set`
    // additionally mandated exact.
    for (ci, (rel, mandated_exact)) in TYPEDARRAY_CALIBRATION_CASES.iter().enumerate() {
        let body = std::fs::read_to_string(env.corpus.join(rel))
            .unwrap_or_else(|e| panic!("read {rel}: {e}"));
        let fm = parse_fm(&body);
        let raw = fm.flags.iter().any(|f| f == "raw");
        let modes: &[bool] = if raw || fm.flags.iter().any(|f| f == "noStrict") {
            &[false]
        } else if fm.flags.iter().any(|f| f == "onlyStrict") {
            &[true]
        } else {
            &[false, true]
        };
        // assert.js + sta.js + frontmatter includes, deduped, in order.
        let include_paths: Vec<PathBuf> = if raw {
            Vec::new()
        } else {
            let mut names: Vec<&str> = vec!["assert.js", "sta.js"];
            for inc in &fm.includes {
                if !names.contains(&inc.as_str()) {
                    names.push(inc);
                }
            }
            names
                .into_iter()
                .map(|n| env.corpus.join("harness").join(n))
                .collect()
        };
        let include_srcs: Vec<String> = include_paths
            .iter()
            .map(|p| std::fs::read_to_string(p).expect("read include"))
            .collect();
        let include_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();
        for &strict in modes {
            let mode = if strict { "strict" } else { "bare" };
            match evaluate_case(&include_refs, &body, strict) {
                InterpOutcome::NoCoverage { reason } => {
                    if *mandated_exact {
                        failures.push(format!(
                            "{rel} [{mode}]: NoCoverage (exactness mandated): {reason}"
                        ));
                    } else {
                        eprintln!("{rel} [{mode}]: sound refusal (accepted): {reason}");
                    }
                }
                InterpOutcome::Trace(mine) => {
                    cmp(
                        &mut failures,
                        &env,
                        &format!("ta-calib-{ci}-{mode}"),
                        rel,
                        mode,
                        &include_paths,
                        &body,
                        strict,
                        &mine,
                    );
                }
            }
        }
    }

    // Focused mandated-exact proof of the includes step-ordering fix (case 1),
    // fully in reach: direct construction, no iterable arg factory.
    {
        let include_paths = vec![env.corpus.join("harness/assert.js"), env.corpus.join("harness/sta.js")];
        let include_srcs: Vec<String> = include_paths
            .iter()
            .map(|p| std::fs::read_to_string(p).expect("read include"))
            .collect();
        let include_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();
        for &strict in &[false, true] {
            let mode = if strict { "strict" } else { "bare" };
            let rel = "<focused includes-len-zero ordering>";
            match evaluate_case(&include_refs, INCLUDES_LEN_ZERO_FOCUSED, strict) {
                InterpOutcome::NoCoverage { reason } => failures.push(format!(
                    "{rel} [{mode}]: NoCoverage (exactness mandated): {reason}"
                )),
                InterpOutcome::Trace(mine) => cmp(
                    &mut failures,
                    &env,
                    &format!("ta-inc-focused-{mode}"),
                    rel,
                    mode,
                    &include_paths,
                    INCLUDES_LEN_ZERO_FOCUSED,
                    strict,
                    &mine,
                ),
            }
        }
    }

    assert!(
        failures.is_empty(),
        "typed-array calibration divergence cases: bar not met:\n{}",
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// (a4) S1f eval calibration divergence cases (S1f2 gate, 2026-07-22): the 23
// cases the recorded gate caught the eval work diverging on, in three
// clusters. Policy (THE BAR): ZERO wrong traces — every covered run is
// trace-equal to Node (or Bun under the either-engine rule), or a sound
// NoCoverage refusal. A `mandated_exact` case additionally forbids refusal.
//
//   * Cluster 1 (sloppy function lexical-vs-variable environment
//     distinctness) — mandated-exact. A NON-strict function body's top-level
//     lexical declarations live in a lexEnv DISTINCT from varEnv (10.2.11
//     step 29), so a body `let x` and a later direct `eval('var x')` collide
//     in EvalDeclarationInstantiation's lexEnv→varEnv conflict walk
//     (SyntaxError). The S1f `var_scope` work had conflated the two frames, so
//     the eval hoisted cleanly and `assert.throws(SyntaxError)` failed. Now
//     exact vs both engines (assert.throws catches the SyntaxError → normal
//     completion). All noStrict → bare only.
//   * Cluster 2 (private name visible to a direct eval) — refuse-or-exact.
//     A direct eval body referencing a private name (`this.#m`) is valid when
//     the enclosing class's PrivateEnvironment declares it; the frozen Script
//     parser has no view of that PrivateEnvironment and rejects the reference,
//     so the eval path REFUSES (NoCoverage) rather than emit a wrong
//     SyntaxError trace (which is what it did before).
//   * Cluster 3 (direct eval with an empty leading/trailing spread) —
//     mandated-exact. `eval(...[], "x=0")` is still a DIRECT eval: the
//     direct/indirect determination is syntactic and a spread does not demote
//     it. ArgumentListEvaluation (iterator side effect included) runs, then the
//     first element is evalText. The gate had gated direct eval to spread-free
//     argument lists, mis-routing these to indirect (global) eval.
// ---------------------------------------------------------------------------

/// (rel path, mandated_exact). `mandated_exact=false` forbids a wrong trace but
/// tolerates the sound NoCoverage refusal (cluster 2).
const S1F2_EVAL_GATE_CASES: [(&str, bool); 23] = [
    // Cluster 1: sloppy-function lexEnv/varEnv distinctness (mandated-exact).
    ("test/language/statements/function/scope-body-lex-distinct.js", true),
    ("test/language/expressions/function/scope-body-lex-distinct.js", true),
    ("test/language/expressions/arrow-function/scope-body-lex-distinct.js", true),
    ("test/language/statements/generators/scope-body-lex-distinct.js", true),
    ("test/language/expressions/generators/scope-body-lex-distinct.js", true),
    ("test/language/expressions/object/scope-meth-body-lex-distinct.js", true),
    ("test/language/expressions/object/scope-gen-meth-body-lex-distinct.js", true),
    ("test/language/expressions/object/scope-getter-body-lex-distinc.js", true),
    ("test/language/expressions/object/scope-setter-body-lex-distinc.js", true),
    // Cluster 3: empty spread in a direct eval call (mandated-exact).
    ("test/language/expressions/call/eval-spread-empty-leading.js", true),
    ("test/language/expressions/call/eval-spread-empty-trailing.js", true),
    // Cluster 2: private name visible to direct eval (refuse-or-exact).
    ("test/language/statements/class/elements/private-field-visible-to-direct-eval.js", false),
    ("test/language/statements/class/elements/private-field-visible-to-direct-eval-on-initializer.js", false),
    ("test/language/statements/class/elements/private-getter-visible-to-direct-eval.js", false),
    ("test/language/statements/class/elements/private-getter-visible-to-direct-eval-on-initializer.js", false),
    ("test/language/statements/class/elements/private-method-visible-to-direct-eval.js", false),
    ("test/language/statements/class/elements/private-method-visible-to-direct-eval-on-initializer.js", false),
    ("test/language/statements/class/elements/private-setter-visible-to-direct-eval.js", false),
    ("test/language/statements/class/elements/private-setter-visible-to-direct-eval-on-initializer.js", false),
    ("test/language/statements/class/elements/private-static-field-visible-to-direct-eval.js", false),
    ("test/language/statements/class/elements/private-static-getter-visible-to-direct-eval.js", false),
    ("test/language/statements/class/elements/private-static-method-visible-to-direct-eval.js", false),
    ("test/language/statements/class/elements/private-static-setter-visible-to-direct-eval.js", false),
];

#[test]
fn s1f2_eval_gate_cases() {
    let Some(env) = env_or_skip("s1f2_eval_gate_cases") else {
        return;
    };
    let mut failures: Vec<String> = Vec::new();
    for (ci, (rel, mandated_exact)) in S1F2_EVAL_GATE_CASES.iter().enumerate() {
        let body = std::fs::read_to_string(env.corpus.join(rel))
            .unwrap_or_else(|e| panic!("read {rel}: {e}"));
        let fm = parse_fm(&body);
        assert!(fm.includes.is_empty(), "{rel}: unexpected extra includes");
        let modes: &[bool] = if fm.flags.iter().any(|f| f == "onlyStrict") {
            &[true]
        } else if fm.flags.iter().any(|f| f == "noStrict" || f == "raw") {
            &[false]
        } else {
            &[false, true]
        };
        let include_paths = vec![
            env.corpus.join("harness/assert.js"),
            env.corpus.join("harness/sta.js"),
        ];
        let include_srcs: Vec<String> = include_paths
            .iter()
            .map(|p| std::fs::read_to_string(p).expect("read include"))
            .collect();
        let include_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();
        for &strict in modes {
            let mode = if strict { "strict" } else { "bare" };
            let mine = match evaluate_case(&include_refs, &body, strict) {
                InterpOutcome::Trace(t) => t,
                InterpOutcome::NoCoverage { reason } => {
                    if *mandated_exact {
                        failures.push(format!(
                            "{rel} [{mode}]: NoCoverage (exactness mandated): {reason}"
                        ));
                    } else {
                        eprintln!("{rel} [{mode}]: sound refusal (accepted): {reason}");
                    }
                    continue;
                }
            };
            match node_trace(&env, &format!("s1f2-{ci}-{mode}"), &include_paths, &body, strict) {
                Ok(node) => {
                    if traces_equal(&mine, &node) {
                        continue;
                    }
                    // Either-engine rule: accept a Bun-equal trace where Node
                    // and Bun themselves disagree.
                    if let Some(bun) = env.bun.clone() {
                        match engine_trace(
                            &env,
                            &bun,
                            &format!("s1f2-{ci}-{mode}-bun"),
                            &include_paths,
                            &body,
                            strict,
                        ) {
                            Ok(bt) if traces_equal(&mine, &bt) => continue,
                            Ok(_) => {}
                            Err(e) => {
                                failures.push(format!("{rel} [{mode}]: bun: {e}"));
                                continue;
                            }
                        }
                    }
                    failures.push(format!(
                        "{rel} [{mode}]: WRONG TRACE: {}",
                        explain_divergence(&mine, &node)
                            .unwrap_or_else(|| "unlocalized".to_string())
                    ));
                }
                Err(e) => failures.push(format!("{rel} [{mode}]: node: {e}")),
            }
        }
    }
    assert!(
        failures.is_empty(),
        "S1f2 eval gate cases: bar not met:\n{}",
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// (b) Corpus sample: zero wrong traces across the S0-eligible sample.
// ---------------------------------------------------------------------------

#[derive(Default)]
struct Fm {
    flags: Vec<String>,
    features: Vec<String>,
    includes: Vec<String>,
}

/// Minimal test262 frontmatter reader for the S0-relevant keys (inline
/// `[a, b]` and dash-list forms).
fn parse_fm(content: &str) -> Fm {
    let mut fm = Fm::default();
    let Some(start) = content.find("/*---") else {
        return fm;
    };
    let Some(end) = content[start..].find("---*/") else {
        return fm;
    };
    let block = &content[start + 5..start + end];
    let lines: Vec<&str> = block.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        let trimmed = line.trim_start();
        let indented = trimmed.len() != line.len();
        if indented || trimmed.is_empty() {
            i += 1;
            continue;
        }
        let Some(colon) = trimmed.find(':') else {
            i += 1;
            continue;
        };
        let key = trimmed[..colon].trim();
        let rest = trimmed[colon + 1..].trim();
        if !matches!(key, "flags" | "features" | "includes") {
            i += 1;
            continue;
        }
        let mut items: Vec<String> = Vec::new();
        if let Some(inner) = rest.strip_prefix('[').and_then(|r| r.strip_suffix(']')) {
            items = inner
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            i += 1;
        } else if rest.is_empty() {
            i += 1;
            while i < lines.len() {
                let l = lines[i].trim();
                if let Some(item) = l.strip_prefix("- ") {
                    items.push(item.trim().to_string());
                    i += 1;
                } else if l.is_empty() {
                    i += 1;
                } else {
                    break;
                }
            }
        } else {
            i += 1;
        }
        match key {
            "flags" => fm.flags = items,
            "features" => fm.features = items,
            _ => fm.includes = items,
        }
    }
    fm
}

/// S0 content rules 4-8 (path rules hold by construction for the sample
/// dirs). Mirrors trust-js-differential/src/slice.rs.
fn s0_eligible(
    content: &str,
    fm: &Fm,
    proposal_features: &std::collections::BTreeSet<String>,
    corpus: &Path,
) -> bool {
    const EXCLUDE_FLAGS: [&str; 4] = ["async", "module", "CanBlockIsTrue", "CanBlockIsFalse"];
    const EXCLUDE_FEATURES: [&str; 7] = [
        "Atomics",
        "SharedArrayBuffer",
        "Temporal",
        "tail-call-optimization",
        "IsHTMLDDA",
        "cross-realm",
        "host-gc-required",
    ];
    if content.contains("$262.") {
        return false;
    }
    if fm.flags.iter().any(|f| EXCLUDE_FLAGS.contains(&f.as_str())) {
        return false;
    }
    if fm
        .features
        .iter()
        .any(|f| EXCLUDE_FEATURES.contains(&f.as_str()) || f.contains("Intl"))
    {
        return false;
    }
    if fm.features.iter().any(|f| proposal_features.contains(f)) {
        return false;
    }
    for inc in &fm.includes {
        let p = corpus.join("harness").join(inc);
        match std::fs::read_to_string(&p) {
            Ok(text) => {
                if text.contains("$262.") {
                    return false;
                }
            }
            Err(_) => return false,
        }
    }
    true
}

fn proposal_features(corpus: &Path) -> std::collections::BTreeSet<String> {
    let text = std::fs::read_to_string(corpus.join("features.txt"))
        .expect("corpus features.txt (S0 rule 7)");
    let mut out = std::collections::BTreeSet::new();
    let mut in_proposed = false;
    for line in text.lines() {
        let t = line.trim();
        if let Some(h) = t.strip_prefix("## ") {
            in_proposed = h == "Proposed language features";
            continue;
        }
        if t.is_empty() || t.starts_with('#') {
            continue;
        }
        if in_proposed {
            out.insert(t.to_string());
        }
    }
    out
}

// ---------------------------------------------------------------------------
// (c) Head-only coverage census over the FULL S0 slice (no node): counts
// covered vs refused runs and the top refusal reasons. Gated on
// TRUST_JS262_CENSUS=1 (it takes a few minutes). Coverage measurement only —
// the four-head calibration remains the divergence authority.
// ---------------------------------------------------------------------------

#[test]
fn full_slice_coverage_census() {
    if std::env::var("TRUST_JS262_CENSUS").ok().as_deref() != Some("1") {
        eprintln!("SKIP full_slice_coverage_census: set TRUST_JS262_CENSUS=1 to run");
        return;
    }
    let corpus = PathBuf::from(
        std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string()),
    );
    assert!(corpus.join("harness/assert.js").is_file(), "corpus not found");
    let proposals = proposal_features(&corpus);
    const EXCLUDE_PREFIXES: [&str; 4] =
        ["test/intl402/", "test/staging/", "test/annexB/", "test/built-ins/Temporal/"];
    let mut rels: Vec<String> = Vec::new();
    let roots_env = std::env::var("TRUST_JS262_CENSUS_ROOT").ok();
    let roots: Vec<&str> = match &roots_env {
        Some(list) => list.split(':').filter(|s| !s.is_empty()).collect(),
        None => vec!["test/language", "test/built-ins"],
    };
    for root in roots {
        let mut stack = vec![corpus.join(root)];
        while let Some(d) = stack.pop() {
            for entry in std::fs::read_dir(&d).expect("read dir") {
                let entry = entry.expect("dir entry");
                let path = entry.path();
                if path.is_dir() {
                    stack.push(path);
                    continue;
                }
                let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
                    continue;
                };
                if !name.ends_with(".js") || name.ends_with("_FIXTURE.js") {
                    continue;
                }
                let rel = path
                    .strip_prefix(&corpus)
                    .expect("under corpus")
                    .to_string_lossy()
                    .replace('\\', "/");
                if EXCLUDE_PREFIXES.iter().any(|p| rel.starts_with(p)) {
                    continue;
                }
                rels.push(rel);
            }
        }
    }
    rels.sort();
    let mut include_cache: std::collections::HashMap<String, String> =
        std::collections::HashMap::new();
    let mut covered = 0u64;
    let mut refused = 0u64;
    let mut reasons: std::collections::HashMap<String, u64> = std::collections::HashMap::new();
    for rel in &rels {
        let Ok(content) = std::fs::read_to_string(corpus.join(rel)) else {
            continue;
        };
        let fm = parse_fm(&content);
        if !s0_eligible(&content, &fm, &proposals, &corpus) {
            continue;
        }
        let raw = fm.flags.iter().any(|f| f == "raw");
        let modes: &[bool] = if raw || fm.flags.iter().any(|f| f == "noStrict") {
            &[false]
        } else if fm.flags.iter().any(|f| f == "onlyStrict") {
            &[true]
        } else {
            &[false, true]
        };
        let include_names: Vec<String> = if raw {
            Vec::new()
        } else {
            let mut names: Vec<&str> = vec!["assert.js", "sta.js"];
            for inc in &fm.includes {
                if !names.contains(&inc.as_str()) {
                    names.push(inc);
                }
            }
            names.into_iter().map(str::to_string).collect()
        };
        for n in &include_names {
            if !include_cache.contains_key(n) {
                let text = std::fs::read_to_string(corpus.join("harness").join(n))
                    .unwrap_or_default();
                include_cache.insert(n.clone(), text);
            }
        }
        let include_refs: Vec<&str> = include_names
            .iter()
            .map(|n| include_cache[n].as_str())
            .collect();
        for &strict in modes {
            match evaluate_case(&include_refs, &content, strict) {
                InterpOutcome::Trace(_) => covered += 1,
                InterpOutcome::NoCoverage { reason } => {
                    refused += 1;
                    *reasons.entry(reason).or_insert(0) += 1;
                }
            }
        }
    }
    let total = covered + refused;
    eprintln!("census: total runs {total}, covered {covered}, refused {refused}");
    let mut rs: Vec<(u64, String)> = reasons.into_iter().map(|(r, n)| (n, r)).collect();
    rs.sort_by(|a, b| b.0.cmp(&a.0));
    for (n, r) in rs.iter().take(30) {
        eprintln!("  {n:>6} × {r}");
    }
}

#[test]
fn corpus_sample_zero_wrong_traces() {
    let Some(env) = env_or_skip("corpus_sample_zero_wrong_traces") else {
        return;
    };
    let proposals = proposal_features(&env.corpus);

    // Collect the S0-eligible sample: per-dir bytewise-sorted rel paths,
    // first `cap` eligible cases of each directory (after an optional skip).
    let cap_override: Option<usize> = std::env::var("TRUST_JS262_SAMPLE_CAP")
        .ok()
        .and_then(|s| s.parse().ok());
    let skip: usize = std::env::var("TRUST_JS262_SAMPLE_SKIP")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    // Optional colon-separated dir-list override for ad-hoc sweeps.
    let dirs_override = std::env::var("TRUST_JS262_SAMPLE_DIRS").ok();
    let dirs: Vec<(String, usize)> = match &dirs_override {
        Some(list) => list
            .split(':')
            .filter(|s| !s.is_empty())
            .map(|d| (d.to_string(), cap_override.unwrap_or(200)))
            .collect(),
        None => SAMPLE_DIRS
            .iter()
            .map(|(d, c)| ((*d).to_string(), cap_override.unwrap_or(*c)))
            .collect(),
    };
    let mut selected: Vec<(String, String, Fm)> = Vec::new();
    for (dir, cap) in dirs {
        let dir = dir.as_str();
        let mut rels: Vec<String> = Vec::new();
        let abs = env.corpus.join(dir);
        let mut stack = vec![abs.clone()];
        while let Some(d) = stack.pop() {
            for entry in std::fs::read_dir(&d).expect("read sample dir") {
                let entry = entry.expect("dir entry");
                let path = entry.path();
                if path.is_dir() {
                    stack.push(path);
                    continue;
                }
                let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
                    continue;
                };
                if !name.ends_with(".js") || name.ends_with("_FIXTURE.js") {
                    continue;
                }
                let rel = path
                    .strip_prefix(&env.corpus)
                    .expect("under corpus")
                    .to_string_lossy()
                    .replace('\\', "/");
                rels.push(rel);
            }
        }
        rels.sort();
        let mut eligible_seen = 0usize;
        let mut taken = 0usize;
        for rel in rels {
            if taken >= cap {
                break;
            }
            let content = std::fs::read_to_string(env.corpus.join(&rel)).expect("read case");
            let fm = parse_fm(&content);
            if s0_eligible(&content, &fm, &proposals, &env.corpus) {
                eligible_seen += 1;
                if eligible_seen <= skip {
                    continue;
                }
                selected.push((rel, content, fm));
                taken += 1;
            }
        }
    }
    eprintln!("corpus sample: {} S0-eligible cases", selected.len());

    let mut covered = 0u32;
    let mut refused = 0u32;
    let mut equal = 0u32;
    let mut failures: Vec<String> = Vec::new();

    for (ci, (rel, body, fm)) in selected.iter().enumerate() {
        let raw = fm.flags.iter().any(|f| f == "raw");
        let modes: &[bool] = if raw || fm.flags.iter().any(|f| f == "noStrict") {
            &[false]
        } else if fm.flags.iter().any(|f| f == "onlyStrict") {
            &[true]
        } else {
            &[false, true]
        };
        // Include assembly per the run-mode contract: raw → none; otherwise
        // assert.js + sta.js + frontmatter includes, deduped, in order.
        let include_paths: Vec<PathBuf> = if raw {
            Vec::new()
        } else {
            let mut names: Vec<&str> = vec!["assert.js", "sta.js"];
            for inc in &fm.includes {
                if !names.contains(&inc.as_str()) {
                    names.push(inc);
                }
            }
            names
                .into_iter()
                .map(|n| env.corpus.join("harness").join(n))
                .collect()
        };
        let include_srcs: Vec<String> = include_paths
            .iter()
            .map(|p| std::fs::read_to_string(p).expect("read include"))
            .collect();
        let include_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();

        for &strict in modes {
            let mode = if strict { "strict" } else { "bare" };
            match evaluate_case(&include_refs, body, strict) {
                InterpOutcome::NoCoverage { reason } => {
                    refused += 1;
                    if std::env::var("TRUST_JS262_PRINT_REFUSED").is_ok() {
                        eprintln!("REFUSED {rel} [{mode}]: {reason}");
                    }
                }
                InterpOutcome::Trace(mine) => {
                    covered += 1;
                    match node_trace(&env, &format!("case-{ci}-{mode}"), &include_paths, body, strict)
                    {
                        Ok(node) => {
                            if traces_equal(&mine, &node) {
                                equal += 1;
                            } else if let Some(bun) = env.bun.clone() {
                                // The four-head consensus rule: where the
                                // engines themselves diverge (audited), the
                                // head matching EITHER engine is equal.
                                match engine_trace(
                                    &env,
                                    &bun,
                                    &format!("case-{ci}-{mode}-bun"),
                                    &include_paths,
                                    body,
                                    strict,
                                ) {
                                    Ok(bt) if traces_equal(&mine, &bt) => {
                                        equal += 1;
                                        eprintln!(
                                            "{rel} [{mode}]: node-divergent, bun-equal \
                                             (audited engine divergence)"
                                        );
                                    }
                                    Ok(_) => failures.push(format!(
                                        "{rel} [{mode}]: WRONG TRACE (both engines): {}",
                                        explain_divergence(&mine, &node)
                                            .unwrap_or_else(|| "unlocalized".to_string())
                                    )),
                                    Err(e) => {
                                        failures.push(format!("{rel} [{mode}]: bun: {e}"));
                                    }
                                }
                            } else {
                                failures.push(format!(
                                    "{rel} [{mode}]: WRONG TRACE: {}",
                                    explain_divergence(&mine, &node)
                                        .unwrap_or_else(|| "unlocalized".to_string())
                                ));
                            }
                        }
                        Err(e) => failures.push(format!("{rel} [{mode}]: node: {e}")),
                    }
                }
            }
        }
    }

    eprintln!(
        "corpus sample runs: covered={covered} refused={refused} equal={equal} wrong={}",
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "corpus sample WRONG TRACES (never acceptable):\n{}",
        failures.join("\n")
    );
}
