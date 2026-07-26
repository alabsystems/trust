// Env-gated adversarial differential for the async job model: Promise object
// model (constructor, then/catch/finally, resolve/reject/all/allSettled/race/
// any, thenable assimilation, @@species), the deterministic microtask +
// virtual-timer drain (micro-before-macro, then-chains, setTimeout ordering,
// queueMicrotask), and async/await (return-a-promise, await tick counts,
// try/catch across await, async-fn-is-not-a-constructor). Every Cover case
// runs through BOTH trust_js_sem::evaluate_case and the real trace driver on
// Node and must be byte-for-byte trace-equal; Refuse cases pin the
// sound-refusal (NoCoverage) behaviour and never consult the driver. Skips
// loudly when TRUST_JS_NODE is unset.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::io::Write;
use std::path::Path;
use std::process::Command;
use trust_js_sem::{evaluate_case, SemOutcome};
use trust_js_trace::{explain_divergence, extract_trace, traces_equal};

#[derive(Clone, Copy, PartialEq)]
enum Expect {
    Cover,
    Refuse,
}

struct Case {
    name: &'static str,
    strict: bool,
    expect: Expect,
    body: &'static str,
}

const C: Expect = Expect::Cover;
const R: Expect = Expect::Refuse;

#[allow(clippy::too_many_lines)]
fn cases() -> Vec<Case> {
    let mut v = Vec::new();
    let mut c = |name: &'static str, strict: bool, expect: Expect, body: &'static str| {
        v.push(Case { name, strict, expect, body });
    };

    // ---- micro-before-macro ordering -------------------------------------
    c("micro-before-macro", false, C,
      "setTimeout(function () { console.log('timeout'); }, 0);\n\
       Promise.resolve().then(function () { console.log('promise'); });\n\
       console.log('sync');");
    c("microtask-chain-drains-before-timer", false, C,
      "setTimeout(function () { console.log('T'); }, 0);\n\
       Promise.resolve().then(function () { console.log('p1'); }).then(function () { console.log('p2'); });");
    c("queuemicrotask-fifo-with-promise", false, C,
      "queueMicrotask(function () { console.log('qm'); });\n\
       Promise.resolve().then(function () { console.log('pr'); });\n\
       console.log('s');");
    c("settimeout-ordering-by-delay", false, C,
      "setTimeout(function () { console.log('100'); }, 100);\n\
       setTimeout(function () { console.log('0'); }, 0);\n\
       setTimeout(function () { console.log('50'); }, 50);");
    c("settimeout-same-delay-insertion-order", false, C,
      "setTimeout(function () { console.log('a'); }, 0);\n\
       setTimeout(function () { console.log('b'); }, 0);\n\
       setTimeout(function () { console.log('c'); }, 0);");
    c("cleartimeout-cancels", false, C,
      "var id = setTimeout(function () { console.log('nope'); }, 0);\n\
       clearTimeout(id);\n\
       setTimeout(function () { console.log('yes'); }, 0);");
    c("nested-timer-runs-after-outer-microtasks", false, C,
      "setTimeout(function () { console.log('t1'); Promise.resolve().then(function () { console.log('t1-micro'); }); setTimeout(function () { console.log('t2'); }, 0); }, 0);\n\
       Promise.resolve().then(function () { console.log('m'); });");

    // ---- then-chains + values --------------------------------------------
    c("then-chain-values", false, C,
      "Promise.resolve(1).then(function (x) { console.log('a' + x); return x + 1; })\n\
       .then(function (x) { console.log('b' + x); });");
    c("then-returns-promise-flattens", false, C,
      "Promise.resolve(1).then(function () { return Promise.resolve('deep'); })\n\
       .then(function (v) { console.log(v); });");
    c("catch-handles-rejection", false, C,
      "Promise.reject('boom').catch(function (e) { console.log('caught ' + e); });");
    c("then-second-handler-rejection", false, C,
      "Promise.reject('x').then(function () { console.log('never'); }, function (e) { console.log('r' + e); });");
    c("finally-passes-through-value", false, C,
      "Promise.resolve(7).finally(function () { console.log('fin'); }).then(function (v) { console.log(v); });");
    c("finally-passes-through-rejection", false, C,
      "Promise.reject('e').finally(function () { console.log('fin'); }).catch(function (e) { console.log('c' + e); });");
    c("reject-then-later-catch", false, C,
      "var p = Promise.reject('late');\n\
       Promise.resolve().then(function () { p.catch(function (e) { console.log('c' + e); }); });");

    // ---- constructor + resolve/reject ------------------------------------
    c("new-promise-executor-resolve", false, C,
      "new Promise(function (res) { res('ok'); }).then(function (v) { console.log(v); });");
    c("new-promise-executor-throw-rejects", false, C,
      "new Promise(function () { throw 'thrown'; }).catch(function (e) { console.log('c' + e); });");
    c("promise-resolve-idempotent-guard", false, C,
      "new Promise(function (res, rej) { res('first'); res('second'); rej('third'); })\n\
       .then(function (v) { console.log(v); });");
    c("promise-instanceof-and-ctor", false, C,
      "var p = Promise.resolve(1);\n\
       console.log(p instanceof Promise, p.constructor === Promise,\n\
       typeof Promise, Promise.length, Promise.name);");
    c("promise-projection", false, C, "Promise.resolve(1);");
    // %Promise.prototype%[@@toStringTag] = "Promise" (27.2.5.5) is a modeled
    // data property: Object.prototype.toString reads it exactly.
    c("promise-tostringtag", false, C,
      "console.log(Object.prototype.toString.call(Promise.resolve(1)));");

    // ---- thenable assimilation -------------------------------------------
    c("thenable-assimilation", false, C,
      "var t = { then: function (res) { console.log('then-called'); res(42); } };\n\
       Promise.resolve(t).then(function (v) { console.log('got ' + v); });");
    c("thenable-rejection", false, C,
      "var t = { then: function (res, rej) { rej('nope'); } };\n\
       Promise.resolve(t).catch(function (e) { console.log('c' + e); });");

    // ---- combinators ------------------------------------------------------
    c("promise-all-values", false, C,
      "Promise.all([1, 2, 3]).then(function (v) { console.log(v.join(',')); });");
    c("promise-all-mixed", false, C,
      "Promise.all([Promise.resolve('x'), 'y', Promise.resolve('z')]).then(function (v) { console.log(v.join(',')); });");
    c("promise-all-reject-short-circuits", false, C,
      "Promise.all([Promise.resolve(1), Promise.reject('bad'), Promise.resolve(3)]).catch(function (e) { console.log('c' + e); });");
    c("promise-all-empty", false, C,
      "Promise.all([]).then(function (v) { console.log(v.length, Array.isArray(v)); });");
    c("promise-allsettled", false, C,
      "Promise.allSettled([Promise.resolve(1), Promise.reject('e')]).then(function (v) { console.log(v[0].status, v[0].value, v[1].status, v[1].reason); });");
    c("promise-race-first-settles", false, C,
      "Promise.race([Promise.resolve('fast'), new Promise(function () {})]).then(function (v) { console.log(v); });");
    c("promise-race-first-rejects", false, C,
      "Promise.race([Promise.reject('fail'), Promise.resolve('slow')]).catch(function (e) { console.log('c' + e); });");
    c("promise-any-first-fulfils", false, C,
      "Promise.any([Promise.reject('a'), Promise.resolve('win')]).then(function (v) { console.log(v); });");

    // ---- async / await ----------------------------------------------------
    c("async-basic-ordering", false, C,
      "async function f() { console.log('1'); await null; console.log('3'); }\n\
       console.log('0'); f(); console.log('2');");
    c("async-two-fns-interleave", false, C,
      "async function a() { console.log('a1'); await 0; console.log('a2'); await 0; console.log('a3'); }\n\
       async function b() { console.log('b1'); await 0; console.log('b2'); await 0; console.log('b3'); }\n\
       a(); b();");
    c("async-returns-promise", false, C,
      "async function f() {}\n\
       var p = f();\n\
       console.log(p instanceof Promise);");
    c("async-return-value", false, C,
      "async function f() { return 5; }\n\
       f().then(function (v) { console.log(v); });");
    c("async-return-promise-assimilates", false, C,
      "async function f() { return Promise.resolve(7); }\n\
       f().then(function (v) { console.log(v); });");
    c("async-await-value", false, C,
      "async function f() { var x = await 41; console.log(x + 1); }\n\
       f();");
    c("async-await-promise", false, C,
      "async function f() { var x = await Promise.resolve('hi'); console.log(x); }\n\
       f();");
    c("async-throw-rejects", false, C,
      "async function f() { throw 'oops'; }\n\
       f().catch(function (e) { console.log('c' + e); });");
    c("async-try-catch-across-await", false, C,
      "async function f() { try { await Promise.reject('e'); console.log('never'); } catch (err) { console.log('caught ' + err); } }\n\
       f();");
    c("async-arrow", false, C,
      "var f = async function () { await 0; console.log('arrow-body'); };\n\
       f();");
    c("async-arrow-concise", false, C,
      "var g = async x => x * 2;\n\
       g(21).then(function (v) { console.log(v); });");
    c("async-not-a-constructor", false, C,
      "async function f() {}\n\
       var t = false; try { new f(); } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t, f.prototype === undefined);");
    // Regression pins (coordinator m2b gate): async functions/arrows in class
    // heritage position.
    c("async-fn-superclass-typeerror", false, C,
      "async function fn() {}\n\
       var t = false; try { class A extends fn {} } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("async-arrow-heritage-syntaxerror-decl", false, C,
      "class C extends async () => {} {}");
    c("async-arrow-heritage-syntaxerror-expr", false, C,
      "var C = class extends async () => {} {};");
    c("async-arrow-ident-heritage-syntaxerror", false, C,
      "class C extends async x => {} {}");
    // An async FUNCTION expression IS a valid LeftHandSideExpression heritage
    // (parses), but is not a constructor → TypeError at class definition.
    c("async-fn-expr-superclass-typeerror", false, C,
      "var t = false; try { class C extends (async function () {}) {} } catch (e) { t = e instanceof TypeError; }\n\
       console.log(t);");
    c("async-await-then-timer", false, C,
      "setTimeout(function () { console.log('timer'); }, 0);\n\
       async function f() { await 0; console.log('after-await'); }\n\
       f();\n\
       console.log('sync');");
    c("await-in-loop", false, C,
      "async function f() { var s = 0; var i = 0; while (i < 3) { s = s + i; await 0; i++; } console.log(s); }\n\
       f();");
    c("await-in-for-of", false, C,
      "async function f() { var out = []; for (var x of [10, 20, 30]) { var y = await x; out.push(y); } console.log(out.join(',')); }\n\
       f();");

    // ---- sound refusals (out of slice) -----------------------------------
    c("await-in-if-test-refuses", false, R,
      "async function f() { if (await true) { console.log('x'); } } f();");
    c("await-in-binary-refuses", false, R,
      "async function f() { return (await 1) + (await 2); } f();");
    c("await-in-call-arg-refuses", false, R,
      "async function f() { console.log(await 1); } f();");
    c("top-level-await-refuses", false, R, "await Promise.resolve(1);");
    c("async-generator-refuses", false, R,
      "async function* f() { yield 1; } f();");
    c("for-await-refuses", false, R,
      "async function f() { for await (var x of [1]) {} } f();");
    c("promise-any-all-reject-refuses", false, R,
      "Promise.any([Promise.reject('a'), Promise.reject('b')]).catch(function () {});");

    v
}

#[test]
#[allow(clippy::too_many_lines)]
fn async_promise_differential_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP async_promise_differential_vs_node: set TRUST_JS_NODE to a node binary");
        return;
    };
    let driver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs");
    assert!(driver.is_file(), "driver not found at {}", driver.display());

    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();
    let mut covered = 0u32;
    let mut refused = 0u32;

    for (ci, case) in cases().iter().enumerate() {
        let sem_body = if case.strict {
            format!("\"use strict\";\n{}", case.body)
        } else {
            case.body.to_string()
        };
        let sem = evaluate_case(&[], &sem_body);
        let sem_trace = match (sem, case.expect) {
            (SemOutcome::NoCoverage { reason }, Expect::Refuse) => {
                refused += 1;
                eprintln!("REFUSES (as pinned) {}: {reason}", case.name);
                continue;
            }
            (SemOutcome::NoCoverage { reason }, Expect::Cover) => {
                failures.push(format!("{}: unexpected NoCoverage: {reason}", case.name));
                continue;
            }
            (SemOutcome::Trace(_), Expect::Refuse) => {
                failures.push(format!("{}: expected a sound refusal but produced a trace", case.name));
                continue;
            }
            (SemOutcome::Trace(t), Expect::Cover) => t,
        };
        covered += 1;

        let body_path = tmp.path().join(format!("async-{ci}.body.js"));
        std::fs::write(&body_path, case.body).expect("write body");
        let manifest = serde_json::json!({
            "completion_witness": true,
            "includes": [],
            "source": body_path.display().to_string(),
            "mode": if case.strict { "strict" } else { "bare" },
            "kind": "script",
        });
        let manifest_path = tmp.path().join(format!("async-{ci}.manifest.json"));
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
        let node_trace = match extract_trace(&out.stdout) {
            Ok(t) => t,
            Err(e) => {
                failures.push(format!(
                    "{}: node driver trace extraction failed: {e} (stderr: {})",
                    case.name,
                    String::from_utf8_lossy(&out.stderr)
                ));
                continue;
            }
        };
        if !traces_equal(&sem_trace, &node_trace) {
            failures.push(format!(
                "{}: DIVERGENCE: {}",
                case.name,
                explain_divergence(&sem_trace, &node_trace).unwrap_or_else(|| "unlocalized".to_string())
            ));
        }
    }

    eprintln!("async/promise differential: {covered} covered, {refused} refused");
    assert!(
        failures.is_empty(),
        "async/promise differential failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
