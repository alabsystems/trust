// Env-gated differential acceptance: run mini-cases through BOTH the
// independent semantics (trust_js_sem::evaluate_case) and the real trace
// driver on Node (trust-js-trace/js/trace_driver.mjs), and require byte-for-
// byte trace equality via trust_js_trace::traces_equal. Skips (loudly) when
// TRUST_JS_NODE is unset; the calibration gate re-runs it with the env set,
// so the skip is not silent overall.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use trust_js_sem::{evaluate_case, evaluate_case_opts, SemOutcome};
use trust_js_trace::{explain_divergence, extract_trace, traces_equal};

// Default corpus root: <repo>/build/js262/test262-<pinned rev>. Derived from
// CARGO_MANIFEST_DIR so it works in any checkout; override with
// TRUST_JS262_CORPUS.
const DEFAULT_CORPUS: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../build/js262/test262-9e61c12835c5e4a3bdba93850427e6742c4f64c4"
);

struct Case {
    name: &'static str,
    with_harness: bool,
    strict: bool,
    body: &'static str,
}

fn cases() -> Vec<Case> {
    vec![
        Case {
            name: "number-repr",
            with_harness: false,
            strict: false,
            body: "console.log(1 + 2, 0.1 + 0.2, 1e21, 1e-7, 5e-324, 123456789, 100, 0.000001, 1.7976931348623157e308);",
        },
        Case {
            name: "negative-zero-nan",
            with_harness: false,
            strict: false,
            body: "console.log(-0, NaN, Infinity, -Infinity, String(-0), 0);",
        },
        Case {
            name: "coercion",
            with_harness: false,
            strict: false,
            body: "console.log('a' + 1, '5' * '2', +true, -'3', 1 + null, 1 + undefined, 'x' + undefined, '' + {}, Number('0x10'), Number(''), Boolean(''), isNaN('abc'));",
        },
        Case {
            name: "comparison-logic",
            with_harness: false,
            strict: false,
            body: "console.log(1 < 2, '10' < '9', 2 <= 2, null == undefined, null === undefined, NaN == NaN, 1 == '1', 0 == false, typeof 5, typeof undefined, typeof null, typeof console.log, true && 0, false || 'x', !1, 1 ? 'a' : 'b');",
        },
        Case {
            name: "loops",
            with_harness: false,
            strict: false,
            body: "var s = 0; for (var i = 0; i < 10; i++) { s += i; } var j = 0; while (j < 3) j++; do j--; while (j > 1); console.log(s, i, j);",
        },
        Case {
            name: "functions-closures",
            with_harness: false,
            strict: false,
            body: "function mk(n) { return function (m) { return n + m; }; } var f = mk(40); console.log(f(2), mk(1)(1), typeof mk, mk.length, f.name);",
        },
        Case {
            name: "try-catch-finally",
            with_harness: false,
            strict: false,
            body: "var r = []; try { r.push('t'); throw 7; } catch (e) { r.push(e); } finally { r.push('f'); } console.log(r);",
        },
        Case {
            name: "string-basics",
            with_harness: false,
            strict: false,
            body: "console.log('abc'.length, 'abc'[1], 'a' < 'b', 'abc' + 'def', 'caf\\u00e9', 'tab\\ttext', 'q\\\"b\\\\s');",
        },
        Case {
            name: "object-array-projection",
            with_harness: false,
            strict: false,
            body: "var o = { b: 1, 2: 'two', a: [1, 2, ['deep']], n: null }; o.self = o; console.log(o, [7, 8], {});",
        },
        Case {
            name: "object-completion",
            with_harness: false,
            strict: false,
            body: "var x = { k: 'v' }; x;",
        },
        Case {
            name: "thrown-native-error",
            with_harness: false,
            strict: false,
            body: "throw new RangeError('r');",
        },
        Case {
            name: "constructor-identity",
            with_harness: false,
            strict: false,
            body: "function A() {} var a = new A(); console.log(a instanceof A, a.constructor === A, typeof A.prototype, a instanceof Object);",
        },
        Case {
            name: "strict-mode-body",
            with_harness: false,
            strict: true,
            body: "var y = 21; y * 2;",
        },
        Case {
            name: "harness-assert-pass",
            with_harness: true,
            strict: false,
            body: "assert.sameValue(1 + 1, 2, 'arith'); assert.notSameValue(-0, 0); assert(true); console.log('ok');",
        },
        Case {
            name: "harness-test262error-throw",
            with_harness: true,
            strict: false,
            body: "assert.sameValue(1, 2, 'boom');",
        },
        Case {
            name: "harness-assert-throws",
            with_harness: true,
            strict: false,
            body: "assert.throws(TypeError, function () { null.x; }); assert.throws(Test262Error, function () { throw new Test262Error('x'); }); console.log('done');",
        },
        Case {
            name: "harness-donotevaluate",
            with_harness: true,
            strict: false,
            body: "$DONOTEVALUATE();",
        },
        // The driver replaces console methods with anonymous recorders and
        // installs its own `print`; the observable name/length/typeof surface
        // must agree.
        Case {
            name: "console-fn-surface",
            with_harness: false,
            strict: false,
            body: "console.log(console.log.name, console.log.length, typeof console.log, print.name, print.length);",
        },
        // slice/indexOf/pop consult inherited elements through the chain.
        Case {
            name: "array-inherited-elements",
            with_harness: false,
            strict: false,
            body: "Array.prototype[1] = 9; var x = [0]; x.length = 2; var s = x.slice(); console.log(s.hasOwnProperty('1'), s[1], x.indexOf(9), x.pop(), x.length);",
        },
        // ArraySpeciesCreate: default constructor, undefined constructor, and
        // the primitive-constructor TypeError.
        Case {
            name: "array-species-paths",
            with_harness: false,
            strict: false,
            body: "var a = [1, 2]; console.log(a.map(function (v) { return v + 1; })); a.constructor = undefined; console.log(a.slice(1)); var b = []; b.constructor = null; try { b.map(function () {}); } catch (e) { console.log(e instanceof TypeError); }",
        },
        // indexOf ordering: length before fromIndex; negative fromIndex.
        Case {
            name: "indexof-order",
            with_harness: false,
            strict: false,
            body: "var p = { valueOf: function () { throw new Error('poison'); } }; console.log([].indexOf(2, p)); var q = { valueOf: function () { return 1; } }; console.log([5, 6, 5].indexOf(5, q), [1, 2].indexOf(2, -1), [1, 2].indexOf(9));",
        },
        // push across the uint32 boundary: index 2^32-2 is the last real
        // element; length 2^32-1 + push lands a plain key then RangeError.
        Case {
            name: "push-uint32-boundary",
            with_harness: false,
            strict: false,
            body: "var x = []; x.length = 4294967294; console.log(x.push('a'), x.length); var y = []; y.length = 4294967295; try { y.push('b'); } catch (e) { console.log(e instanceof RangeError, y[4294967295], y.length); }",
        },
        // Error.prototype.toString composition (name/message joining) and
        // the Default-hint ToPrimitive path on error instances.
        Case {
            name: "error-tostring",
            with_harness: false,
            strict: false,
            body: "console.log(new TypeError('x').toString(), String(new RangeError('')), '' + new Error('e'));",
        },
        // Strict assignment to the non-writable own `length` of a function
        // throws; the modeled name/length attributes are the real ones.
        Case {
            name: "strict-nonwritable-fn-length",
            with_harness: false,
            strict: true,
            body: "function f(a, b) {} var t = false; try { f.length = 5; } catch (e) { t = e instanceof TypeError; } console.log(t, f.length, f.name);",
        },
        // Reference records coerce a computed key at most ONCE (GetValue
        // caches it for the following PutValue in compound/update forms).
        Case {
            name: "refkey-coerce-once",
            with_harness: false,
            strict: false,
            body: "var n = 0; var o = {}; var p = { toString: function () { n++; return 'k'; } }; o[p] += 1; var m = 0; var q = { toString: function () { m++; return 'j'; } }; o[q]++; console.log(n, m, o.k, o.j);",
        },
        // Null base: key and right-hand side evaluate before PutValue's
        // TypeError.
        Case {
            name: "member-null-late-typeerror",
            with_harness: false,
            strict: false,
            body: "var order = []; function k() { order.push('k'); return 'p'; } var base = null; var t1 = false; try { base[k()] = order.push('rhs'); } catch (e) { t1 = e instanceof TypeError; } console.log(t1, order);",
        },
    ]
}

#[test]
fn bootstrap_differential_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!(
            "SKIP bootstrap_differential_vs_node: set TRUST_JS_NODE to a node binary \
             (and optionally TRUST_JS262_CORPUS) to run the Node differential"
        );
        return;
    };
    let corpus = std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string());
    let corpus = PathBuf::from(corpus);
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

    let assert_path = corpus.join("harness/assert.js");
    let sta_path = corpus.join("harness/sta.js");
    let assert_src = std::fs::read_to_string(&assert_path).expect("read assert.js");
    let sta_src = std::fs::read_to_string(&sta_path).expect("read sta.js");

    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();

    for case in cases() {
        // Head 1: the independent semantics. The caller applies strict mode
        // by prepending the directive, exactly as the driver does.
        let sem_body = if case.strict {
            format!("\"use strict\";\n{}", case.body)
        } else {
            case.body.to_string()
        };
        let includes_src: Vec<&str> = if case.with_harness {
            vec![assert_src.as_str(), sta_src.as_str()]
        } else {
            Vec::new()
        };
        let sem = evaluate_case(&includes_src, &sem_body);
        let sem_trace = match sem {
            SemOutcome::Trace(t) => t,
            SemOutcome::NoCoverage { reason } => {
                failures.push(format!("{}: NoCoverage: {reason}", case.name));
                continue;
            }
        };

        // Head 2: the real driver on Node. The pristine body goes to disk;
        // the driver itself applies the strict prefix per the manifest.
        let body_path = tmp.path().join(format!("{}.body.js", case.name));
        std::fs::write(&body_path, case.body).expect("write body");
        let includes_json: Vec<String> = if case.with_harness {
            vec![
                assert_path.display().to_string(),
                sta_path.display().to_string(),
            ]
        } else {
            Vec::new()
        };
        let manifest = serde_json::json!({
            "completion_witness": true,
            "includes": includes_json,
            "source": body_path.display().to_string(),
            "mode": if case.strict { "strict" } else { "bare" },
            "kind": "script",
        });
        let manifest_path = tmp.path().join(format!("{}.manifest.json", case.name));
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
                explain_divergence(&sem_trace, &node_trace)
                    .unwrap_or_else(|| "unlocalized".to_string())
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "bootstrap differential failures:\n{}",
        failures.join("\n")
    );
}

/// Corpus cases from the 2026-07 calibration where the sem head previously
/// produced a WRONG trace (its assertion evaluation threw Test262Error while
/// Node/Bun completed normally) due to intrinsic-model gaps. The soundness
/// bar: for each case, in each mode, the sem head must either refuse
/// (NoCoverage) or emit a trace byte-for-byte equal to the Node driver's.
/// A wrong trace fails; a refusal is sound and is logged loudly.
const SOUNDNESS_CORPUS_CASES: &[&str] = &[
    "test/built-ins/Array/prototype/indexOf/length-zero-returns-minus-one.js",
    "test/built-ins/Array/prototype/map/create-ctor-non-object.js",
    "test/built-ins/Array/prototype/push/S15.4.4.7_A3.js",
    "test/built-ins/Array/prototype/slice/create-ctor-non-object.js",
    "test/built-ins/Array/prototype/slice/S15.4.4.10_A4_T1.js",
    "test/built-ins/Array/prototype/toLocaleString/S15.4.4.3_A1_T1.js",
    "test/built-ins/Array/prototype/toLocaleString/S15.4.4.3_A3_T1.js",
    "test/built-ins/Boolean/S15.6.3_A1.js",
    "test/built-ins/Function/prototype/toString/S15.3.4.2_A12.js",
    "test/built-ins/Function/prototype/toString/S15.3.4.2_A13.js",
    "test/built-ins/Function/prototype/toString/S15.3.4.2_A14.js",
    "test/built-ins/Function/prototype/toString/S15.3.4.2_A16.js",
    "test/built-ins/Number/S15.7.3_A1.js",
    // --- 2026-07-21 full-calibration remainder (50 cases) ---
    // Family A: reference semantics (deferred base validation + ToPropertyKey).
    "test/language/expressions/assignment/target-member-computed-reference.js",
    "test/language/expressions/assignment/target-member-computed-reference-null.js",
    "test/language/expressions/assignment/target-member-computed-reference-undefined.js",
    "test/language/expressions/assignment/target-member-identifier-reference-null.js",
    "test/language/expressions/assignment/target-member-identifier-reference-undefined.js",
    "test/language/expressions/compound-assignment/S11.13.2_A7.1_T1.js",
    "test/language/expressions/compound-assignment/S11.13.2_A7.1_T2.js",
    "test/language/expressions/compound-assignment/S11.13.2_A7.2_T1.js",
    "test/language/expressions/compound-assignment/S11.13.2_A7.2_T2.js",
    "test/language/expressions/compound-assignment/S11.13.2_A7.3_T1.js",
    "test/language/expressions/compound-assignment/S11.13.2_A7.3_T2.js",
    "test/language/expressions/compound-assignment/S11.13.2_A7.4_T1.js",
    "test/language/expressions/compound-assignment/S11.13.2_A7.4_T2.js",
    "test/language/expressions/compound-assignment/S11.13.2_A7.5_T1.js",
    "test/language/expressions/compound-assignment/S11.13.2_A7.5_T2.js",
    "test/language/expressions/postfix-decrement/S11.3.2_A6_T1.js",
    "test/language/expressions/postfix-decrement/S11.3.2_A6_T2.js",
    "test/language/expressions/postfix-increment/S11.3.1_A6_T1.js",
    "test/language/expressions/postfix-increment/S11.3.1_A6_T2.js",
    "test/language/expressions/prefix-decrement/S11.4.5_A6_T1.js",
    "test/language/expressions/prefix-decrement/S11.4.5_A6_T2.js",
    "test/language/expressions/prefix-increment/S11.4.4_A6_T1.js",
    "test/language/expressions/prefix-increment/S11.4.4_A6_T2.js",
    // Family B: strict early errors (exact SyntaxError at parse).
    "test/language/expressions/function/name-arguments-strict-body.js",
    "test/language/expressions/function/name-eval-strict-body.js",
    "test/language/expressions/function/param-eval-strict-body.js",
    "test/language/statements/function/name-arguments-strict-body.js",
    "test/language/statements/function/name-eval-strict-body.js",
    "test/language/statements/function/param-arguments-strict-body.js",
    "test/language/statements/function/param-eval-strict-body.js",
    "test/language/expressions/postfix-decrement/arguments.js",
    "test/language/expressions/postfix-decrement/eval.js",
    "test/language/expressions/postfix-increment/11.3.1-2-1gs.js",
    "test/language/expressions/postfix-increment/arguments.js",
    "test/language/expressions/postfix-increment/eval.js",
    "test/language/expressions/prefix-decrement/11.4.5-2-2gs.js",
    "test/language/expressions/prefix-decrement/arguments.js",
    "test/language/expressions/prefix-decrement/eval.js",
    "test/language/expressions/prefix-increment/arguments.js",
    "test/language/expressions/prefix-increment/eval.js",
    "test/language/expressions/object/__proto__-duplicate.js",
    // ...but the SAME duplicate inside an ObjectAssignmentPattern is LEGAL
    // (B.3.1 covers only ObjectLiteral initializers): engines complete
    // normally, so sem must not guess a SyntaxError — destructuring is out
    // of slice, so the sound outcome is NoCoverage.
    "test/language/expressions/assignment/destructuring/obj-prop-__proto__dup.js",
    "test/language/statements/try/early-catch-lex.js",
    // Family C: arguments-object surface (refuses in functions).
    "test/language/arguments-object/10.6-6-3.js",
    "test/language/arguments-object/10.6-6-4.js",
    "test/language/statements/function/S13_A15_T4.js",
    "test/language/statements/function/S13_A15_T5.js",
    // Family D: TDZ writes through closures.
    "test/language/statements/let/function-local-closure-set-before-initialization.js",
    "test/language/statements/let/global-closure-set-before-initialization.js",
    // Family E: fn-name reassignment no-op; OrdinaryHasInstance order.
    "test/language/expressions/function/named-no-strict-reassign-fn-name-in-body.js",
    "test/language/expressions/instanceof/primitive-prototype-with-primitive.js",
];

/// The 2026-07-21 s1b-gate sem divergences (12 runs / 7 cases), pinned as
/// regressions. `true` = the case MUST produce a trace (and match the driver
/// byte-for-byte — the four parse cases are exact SyntaxError traces, the
/// two S13_A15 cases run to completion); `false` = exact-or-refuse (the
/// Symbol.hasInstance case soundly refuses at the `Symbol` global).
const GATE_S1B_REGRESSION_CASES: &[(&str, bool)] = &[
    // --- 2026-07-21 s1c-gate tail (16 runs / 8 cases), all mandated exact:
    // the four parse cases are exact SyntaxError traces (arrow/CPEAAPL
    // assignment-target and heritage early errors); the four acceptance
    // cases run to completion (super in method param defaults, escaped
    // `await` class name, escaped function names).
    (
        "test/language/expressions/assignmenttargettype/direct-arrowfunction-1.js",
        true,
    ),
    (
        "test/language/expressions/assignmenttargettype/parenthesized-primaryexpression-objectliteral.js",
        true,
    ),
    (
        "test/language/statements/class/elements/syntax/early-errors/class-heritage-array-literal-arrow-heritage.js",
        true,
    ),
    (
        "test/language/expressions/class/elements/syntax/early-errors/class-heritage-array-literal-arrow-heritage.js",
        true,
    ),
    (
        "test/language/expressions/object/method-definition/name-super-prop-param.js",
        true,
    ),
    ("test/language/statements/class/class-name-ident-await-escaped.js", true),
    ("test/language/statements/function/S14_A5_T1.js", true),
    ("test/language/statements/function/S14_A5_T2.js", true),
    (
        "test/built-ins/Function/prototype/Symbol.hasInstance/this-val-poisoned-prototype.js",
        false,
    ),
    ("test/language/statements/for-of/head-decl-no-expr.js", true),
    ("test/language/statements/for-of/head-expr-no-expr.js", true),
    ("test/language/statements/for-of/head-var-no-expr.js", true),
    ("test/language/statements/for-of/head-lhs-async-invalid.js", true),
    ("test/language/statements/function/S13_A15_T1.js", true),
    ("test/language/statements/function/S13_A15_T3.js", true),
];

#[test]
fn gate_s1b_regression_cases_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!(
            "SKIP gate_s1b_regression_cases_vs_node: set TRUST_JS_NODE to a node binary to run"
        );
        return;
    };
    let corpus = std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string());
    let corpus = PathBuf::from(corpus);
    let driver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs");
    let assert_path = corpus.join("harness/assert.js");
    let sta_path = corpus.join("harness/sta.js");
    let assert_src = std::fs::read_to_string(&assert_path).expect("read assert.js");
    let sta_src = std::fs::read_to_string(&sta_path).expect("read sta.js");
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();

    for (ci, (rel, must_cover)) in GATE_S1B_REGRESSION_CASES.iter().enumerate() {
        let case_path = corpus.join(rel);
        let body = std::fs::read_to_string(&case_path)
            .unwrap_or_else(|e| panic!("read gate case {rel}: {e}"));
        for &strict in case_modes(&body) {
            let mode = if strict { "strict" } else { "bare" };
            let sem_body = if strict {
                format!("\"use strict\";\n{body}")
            } else {
                body.clone()
            };
            let sem = evaluate_case_opts(&[&assert_src, &sta_src], &sem_body, false);
            let sem_trace = match sem {
                SemOutcome::Trace(t) => t,
                SemOutcome::NoCoverage { reason } => {
                    if *must_cover {
                        failures.push(format!(
                            "{rel} [{mode}]: must produce a trace but refused: {reason}"
                        ));
                    } else {
                        eprintln!("SOUND REFUSAL {rel} [{mode}]: {reason}");
                    }
                    continue;
                }
            };

            let body_path = tmp.path().join(format!("gate-{ci}.body.js"));
            std::fs::write(&body_path, &body).expect("write body");
            let manifest = serde_json::json!({
                "completion_witness": false,
                "includes": [
                    assert_path.display().to_string(),
                    sta_path.display().to_string(),
                ],
                "source": body_path.display().to_string(),
                "mode": mode,
                "kind": "script",
            });
            let manifest_path = tmp.path().join(format!("gate-{ci}.{mode}.manifest.json"));
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
                        "{rel} [{mode}]: node driver trace extraction failed: {e}"
                    ));
                    continue;
                }
            };
            if !traces_equal(&sem_trace, &node_trace) {
                failures.push(format!(
                    "{rel} [{mode}]: WRONG TRACE: {}",
                    explain_divergence(&sem_trace, &node_trace)
                        .unwrap_or_else(|| "unlocalized".to_string())
                ));
            }
        }
    }

    assert!(
        failures.is_empty(),
        "s1b gate regression failures:\n{}",
        failures.join("\n")
    );
}

/// Modes a case runs in, from its frontmatter flags (mirrors the calibration
/// harness): `onlyStrict` → strict only, `noStrict`/`raw` → bare only,
/// otherwise both.
fn case_modes(body: &str) -> &'static [bool] {
    let fm = body
        .split_once("/*---")
        .and_then(|(_, rest)| rest.split_once("---*/"))
        .map_or("", |(fm, _)| fm);
    let flags = fm
        .lines()
        .find(|l| l.trim_start().starts_with("flags:"))
        .unwrap_or("");
    if flags.contains("onlyStrict") {
        &[true]
    } else if flags.contains("noStrict") || flags.contains("raw") {
        &[false]
    } else {
        &[false, true]
    }
}

#[test]
fn corpus_soundness_cases_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!(
            "SKIP corpus_soundness_cases_vs_node: set TRUST_JS_NODE to a node binary \
             (and optionally TRUST_JS262_CORPUS) to run the corpus differential"
        );
        return;
    };
    let corpus = std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string());
    let corpus = PathBuf::from(corpus);
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

    let assert_path = corpus.join("harness/assert.js");
    let sta_path = corpus.join("harness/sta.js");
    let assert_src = std::fs::read_to_string(&assert_path).expect("read assert.js");
    let sta_src = std::fs::read_to_string(&sta_path).expect("read sta.js");

    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();

    for (ci, rel) in SOUNDNESS_CORPUS_CASES.iter().enumerate() {
        let case_path = corpus.join(rel);
        let body = std::fs::read_to_string(&case_path)
            .unwrap_or_else(|e| panic!("read corpus case {rel}: {e}"));
        // None of these cases carry extra frontmatter includes: the includes
        // are the default assert.js + sta.js. Modes follow the frontmatter
        // flags, exactly like the calibration harness (completion witness
        // off).
        for &strict in case_modes(&body) {
            let mode = if strict { "strict" } else { "bare" };
            let sem_body = if strict {
                format!("\"use strict\";\n{body}")
            } else {
                body.clone()
            };
            let sem = evaluate_case_opts(&[&assert_src, &sta_src], &sem_body, false);
            let sem_trace = match sem {
                SemOutcome::Trace(t) => t,
                SemOutcome::NoCoverage { reason } => {
                    eprintln!("SOUND REFUSAL {rel} [{mode}]: {reason}");
                    continue;
                }
            };

            let body_path = tmp.path().join(format!("case-{ci}.body.js"));
            std::fs::write(&body_path, &body).expect("write body");
            let manifest = serde_json::json!({
                "completion_witness": false,
                "includes": [
                    assert_path.display().to_string(),
                    sta_path.display().to_string(),
                ],
                "source": body_path.display().to_string(),
                "mode": mode,
                "kind": "script",
            });
            let manifest_path = tmp.path().join(format!("case-{ci}.{mode}.manifest.json"));
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
                        "{rel} [{mode}]: node driver trace extraction failed: {e} (stderr: {})",
                        String::from_utf8_lossy(&out.stderr)
                    ));
                    continue;
                }
            };

            if !traces_equal(&sem_trace, &node_trace) {
                failures.push(format!(
                    "{rel} [{mode}]: WRONG TRACE: {}",
                    explain_divergence(&sem_trace, &node_trace)
                        .unwrap_or_else(|| "unlocalized".to_string())
                ));
            }
        }
    }

    assert!(
        failures.is_empty(),
        "corpus soundness failures (wrong trace is never acceptable):\n{}",
        failures.join("\n")
    );
}
