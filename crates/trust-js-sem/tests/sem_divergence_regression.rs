// Regression pins for the 37 four-head sem-divergent runs the recorded
// calibration-s1d gate found (build/js262/calibration-s1d-gate/
// sem_divergences.jsonl). Seven clusters, all previously WRONG traces in
// trust-js-sem:
//
//   1. Class-heritage private-name early errors (ClassHeritage evaluates in the
//      OUTER PrivateEnvironment, so the class's own `#name` is undeclared
//      there → early SyntaxError).                          -> ParseSyntaxError
//   2. GeneratorFunction subclassing (`class C extends %GeneratorFunction%`):
//      exotic dynamic-source instance creation is out of slice -> Refuse.
//   3. `yield` in a generator/arrow-in-generator parameter default (a
//      YieldExpression in FormalParameters), and strict `yield` as a parameter
//      IdentifierReference.                                  -> ParseSyntaxError
//   4. `({* foo})` — a `*` generator prefix with no parameter list.
//                                                            -> ParseSyntaxError
//   5. Object.prototype.toString on generators (@@toStringTag "Generator" /
//      "GeneratorFunction" — symbol-keyed, unmodeled)          -> Refuse.
//
// Two dispositions:
//   * ParseSyntaxError — sem must emit a driver-equal parse-phase SyntaxError
//     trace (constructor identity `SyntaxError`, no message).
//   * Refuse — sem must return a sound NoCoverage (never a wrong TypeError /
//     Test262Error).
//
// The plain tests below run without Node (inline snippets + a corpus-parse
// sweep gated only on corpus presence). The env-gated `..._vs_node` test runs
// the exact pinned files through BOTH sem and the Node trace driver and
// requires trace-equality for the parse cases and NoCoverage for the refuse
// cases — a wrong trace is gate-fatal.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use trust_js_sem::{evaluate_case, evaluate_case_opts, SemOutcome};
use trust_js_trace::{
    extract_trace, traces_equal, Completion, ProjectedValue, ThrownProjection,
};

// Default corpus root: <repo>/build/js262/test262-<pinned rev>. Derived from
// CARGO_MANIFEST_DIR so it works in any checkout; override with
// TRUST_JS262_CORPUS.
const DEFAULT_CORPUS: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../build/js262/test262-9e61c12835c5e4a3bdba93850427e6742c4f64c4"
);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Disp {
    /// sem must emit an exact parse-phase SyntaxError trace.
    ParseSyntaxError,
    /// sem must return a sound NoCoverage refusal (never a wrong trace).
    Refuse,
}

/// Every unique divergent file with its ruled disposition. Modes (bare/strict)
/// are derived from each file's frontmatter flags, exactly like the corpus
/// runners, so onlyStrict / noStrict cases run only their applicable mode.
const PINS: &[(&str, Disp)] = &[
    // -- Cluster 1: class-heritage private-name early errors -----------------
    (
        "test/language/expressions/class/elements/syntax/early-errors/grammar-private-environment-on-class-heritage.js",
        Disp::ParseSyntaxError,
    ),
    (
        "test/language/expressions/class/elements/syntax/early-errors/grammar-private-environment-on-class-heritage-recursive.js",
        Disp::ParseSyntaxError,
    ),
    (
        "test/language/expressions/class/elements/syntax/early-errors/grammar-private-environment-on-class-heritage-chained-usage.js",
        Disp::ParseSyntaxError,
    ),
    (
        "test/language/expressions/class/elements/syntax/early-errors/grammar-private-environment-on-class-heritage-function-expression.js",
        Disp::ParseSyntaxError,
    ),
    (
        "test/language/statements/class/elements/syntax/early-errors/grammar-private-environment-on-class-heritage.js",
        Disp::ParseSyntaxError,
    ),
    (
        "test/language/statements/class/elements/syntax/early-errors/grammar-private-environment-on-class-heritage-recursive.js",
        Disp::ParseSyntaxError,
    ),
    (
        "test/language/statements/class/elements/syntax/early-errors/grammar-private-environment-on-class-heritage-chained-usage.js",
        Disp::ParseSyntaxError,
    ),
    (
        "test/language/statements/class/elements/syntax/early-errors/grammar-private-environment-on-class-heritage-function-expression.js",
        Disp::ParseSyntaxError,
    ),
    // -- Cluster 3: yield in generator/arrow parameter defaults --------------
    (
        "test/language/expressions/arrow-function/param-dflt-yield-expr.js",
        Disp::ParseSyntaxError,
    ),
    (
        "test/language/expressions/function/param-dflt-yield-strict.js",
        Disp::ParseSyntaxError,
    ),
    (
        "test/language/statements/function/param-dflt-yield-strict.js",
        Disp::ParseSyntaxError,
    ),
    (
        "test/language/expressions/object/method-definition/generator-param-init-yield.js",
        Disp::ParseSyntaxError,
    ),
    // -- Cluster 4: `({* foo})` -----------------------------------------------
    (
        "test/language/expressions/object/prop-def-invalid-star-prefix.js",
        Disp::ParseSyntaxError,
    ),
    // -- Cluster 2: GeneratorFunction subclassing (refuse) -------------------
    (
        "test/language/statements/class/subclass/builtin-objects/GeneratorFunction/instance-length.js",
        Disp::Refuse,
    ),
    (
        "test/language/statements/class/subclass/builtin-objects/GeneratorFunction/instance-name.js",
        Disp::Refuse,
    ),
    (
        "test/language/statements/class/subclass/builtin-objects/GeneratorFunction/instance-prototype.js",
        Disp::Refuse,
    ),
    (
        "test/language/statements/class/subclass/builtin-objects/GeneratorFunction/regular-subclassing.js",
        Disp::Refuse,
    ),
    (
        "test/language/statements/class/subclass/builtin-objects/GeneratorFunction/super-must-be-called.js",
        Disp::Refuse,
    ),
    // superclass-generator-function.js was a Refuse pin only because `new
    // Proxy(...)` used to refuse; with the Proxy exotic implemented it now
    // COVERS correctly (all three assert.throws(TypeError) pass — IsConstructor
    // is false for a generator function, a bound generator function, and a
    // proxy over one — so it is no longer a pinned divergence).
    // -- Cluster 5: Object.prototype.toString on generators (refuse) ---------
    (
        "test/built-ins/Object/prototype/toString/symbol-tag-generators-builtin.js",
        Disp::Refuse,
    ),
];

/// A parse-phase SyntaxError throw, exactly as a conforming engine (and the
/// driver) projects it: constructor identity only, no message text.
fn is_syntax_error_trace(o: &SemOutcome) -> bool {
    let SemOutcome::Trace(t) = o else {
        return false;
    };
    matches!(
        &t.completion,
        Completion::Throw {
            v: ThrownProjection::Error { ctor, name, ctor_name },
            phase: None,
        } if ctor.as_deref() == Some("Error:SyntaxError")
            && name.as_deref() == Some("SyntaxError")
            && ctor_name.as_deref() == Some("SyntaxError")
    )
}

fn is_type_error_throw(o: &SemOutcome) -> bool {
    matches!(
        o,
        SemOutcome::Trace(t) if matches!(&t.completion, Completion::Throw {
            v: ThrownProjection::Error { name: Some(n), .. }, ..
        } if n == "TypeError")
    )
}

// ---------------------------------------------------------------------------
// Plain inline tests (no Node): representative snippets for every cluster.
// ---------------------------------------------------------------------------

#[test]
fn cluster1_heritage_private_name_is_syntax_error() {
    // A `#name` referenced in the ClassHeritage resolves against the OUTER
    // PrivateEnvironment (where the class's own `#foo` is NOT declared).
    for src in [
        "class C extends class { x = this.#foo; } { #foo; }",
        "class C extends class extends class { x = this.#foo; } {} { #foo; }",
        "class C extends function() { this.#foo; } { #foo; }",
        // Expression form.
        "(class C extends class { x = this.#foo; } { #foo; });",
        // Chained: the innermost heritage reference is undeclared at every
        // level (each nested heritage sees only its own OUTER env).
        "class C extends class extends class extends class { x = this.#foo; } { #foo; x = this.#bar; } { #bar; x = this.#fuz; } { #fuz; }",
    ] {
        assert!(
            is_syntax_error_trace(&evaluate_case(&[], src)),
            "expected SyntaxError trace for: {src}\n got {:?}",
            evaluate_case(&[], src)
        );
    }
    // A private name legitimately referenced in the BODY (not the heritage) of
    // its own class still resolves — the fix must not over-reject.
    assert!(matches!(
        evaluate_case(&[], "class C { #foo = 1; m() { return this.#foo; } } new C().m();"),
        SemOutcome::Trace(t) if matches!(t.completion, Completion::Normal { .. })
    ));
    // An OUTER class's private name IS visible in a nested class's heritage
    // (the fix must not bubble it PAST the enclosing class): this must NOT be
    // rejected as an undeclared-private SyntaxError.
    let outer_ref = evaluate_case(
        &[],
        "class Base {}\nclass O { #p = 1; m() { class I extends (#p in this ? Base : Base) {} return new I(); } }\nnew O().m();",
    );
    assert!(
        matches!(&outer_ref, SemOutcome::Trace(t) if matches!(t.completion, Completion::Normal { .. })),
        "outer private name in nested heritage should resolve, got {outer_ref:?}"
    );
}

#[test]
fn cluster3_yield_in_generator_params_is_syntax_error() {
    // Arrow parameters inside a generator are [+Yield]: a YieldExpression there
    // is an early error.
    assert!(is_syntax_error_trace(&evaluate_case(
        &[],
        "function *g() { (x = yield) => {}; }"
    )));
    // Generator method's own parameters are [+Yield].
    assert!(is_syntax_error_trace(&evaluate_case(
        &[],
        "({ *method(x = yield) {} });"
    )));
    // A generator function's OWN parameters are [+Yield].
    assert!(is_syntax_error_trace(&evaluate_case(
        &[],
        "function* g(x = yield) {}"
    )));
    // Strict-mode `yield` as a parameter IdentifierReference in a non-generator
    // nested function.
    assert!(is_syntax_error_trace(&evaluate_case(
        &[],
        "\"use strict\";\nfunction *g() { 0, function(x = yield) {}; }"
    )));
    assert!(is_syntax_error_trace(&evaluate_case(
        &[],
        "\"use strict\";\nfunction *g() { function f(x = yield) {} }"
    )));
    // Soundness guard: in SLOPPY code a non-generator nested function's
    // parameter `yield` is an ordinary identifier — NOT a false SyntaxError.
    // (sem's sloppy `yield`-as-identifier is out of slice, so this refuses.)
    assert!(matches!(
        evaluate_case(&[], "function *g() { function f(x = yield) {} }"),
        SemOutcome::NoCoverage { .. }
    ));
}

#[test]
fn cluster4_star_prefix_object_prop_is_syntax_error() {
    assert!(is_syntax_error_trace(&evaluate_case(&[], "({* foo});")));
    // A proper generator method still parses and runs.
    assert!(matches!(
        evaluate_case(&[], "var o = { *g() { yield 1; } }; var it = o.g(); it.next().value;"),
        SemOutcome::Trace(t) if matches!(t.completion, Completion::Normal { .. })
    ));
}

#[test]
fn cluster2_generator_function_subclassing_refuses() {
    // `class C extends %GeneratorFunction% {}` — the dynamic-source generator
    // constructor is out of slice: refuse, never a wrong TypeError.
    assert!(matches!(
        evaluate_case(
            &[],
            "var GF = Object.getPrototypeOf(function*(){}).constructor;\nclass C extends GF {}"
        ),
        SemOutcome::NoCoverage { .. }
    ));
}

#[test]
fn generator_instance_is_not_a_constructor() {
    // A generator function INSTANCE has no [[Construct]] — `extends` it throws
    // TypeError (superclass-generator-function.js: IsConstructor before the
    // "prototype" lookup).
    assert!(is_type_error_throw(&evaluate_case(
        &[],
        "function* fn() {}\nclass A extends fn {}"
    )));
    // And `new` on a generator function throws TypeError.
    assert_eq!(
        completion_of(evaluate_case(
            &[],
            "var t = false;\ntry { new (function*(){})(); } catch (e) { t = e instanceof TypeError; }\nt;"
        )),
        Completion::Normal {
            v: Some(ProjectedValue::Bool { v: true })
        }
    );
}

#[test]
fn cluster5_object_tostring_on_generator_refuses() {
    // Generator function @@toStringTag "GeneratorFunction" is symbol-keyed and
    // unmodeled: refuse, never the plain "[object Function]".
    assert!(matches!(
        evaluate_case(&[], "Object.prototype.toString.call(function*(){});"),
        SemOutcome::NoCoverage { .. }
    ));
    // Generator instance @@toStringTag "Generator" is likewise refused.
    assert!(matches!(
        evaluate_case(&[], "Object.prototype.toString.call((function*(){})());"),
        SemOutcome::NoCoverage { .. }
    ));
}

fn completion_of(o: SemOutcome) -> Completion {
    match o {
        SemOutcome::Trace(t) => t.completion,
        SemOutcome::NoCoverage { reason } => panic!("unexpected NoCoverage: {reason}"),
    }
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
// Plain corpus-parse sweep (no Node): each pinned file's local disposition.
// ---------------------------------------------------------------------------

#[test]
fn pinned_divergences_local_disposition() {
    let Some(corpus) = corpus_root() else {
        eprintln!("SKIP pinned_divergences_local_disposition: corpus not present");
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
                Disp::ParseSyntaxError => is_syntax_error_trace(&out),
                Disp::Refuse => matches!(out, SemOutcome::NoCoverage { .. }),
            };
            if !ok {
                failures.push(format!("{rel} [{mode}]: expected {disp:?}, got {out:?}"));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "pinned local dispositions ({} of {checked} checks failed):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Env-gated differential vs the Node trace driver.
// ---------------------------------------------------------------------------

#[test]
#[allow(clippy::too_many_lines)]
fn pinned_divergences_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP pinned_divergences_vs_node: set TRUST_JS_NODE to run");
        return;
    };
    let Some(corpus) = corpus_root() else {
        eprintln!("SKIP pinned_divergences_vs_node: corpus not present");
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
    let mut refused = 0u64;
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

            // Disposition contract, checked FIRST (independent of Node).
            match (disp, &sem) {
                (Disp::ParseSyntaxError, _) if !is_syntax_error_trace(&sem) => {
                    failures.push(format!(
                        "{rel} [{mode}]: expected parse SyntaxError, got {sem:?}"
                    ));
                    continue;
                }
                (Disp::Refuse, SemOutcome::Trace(t)) => {
                    failures.push(format!(
                        "{rel} [{mode}]: expected NoCoverage refusal, got trace {:?}",
                        t.completion
                    ));
                    continue;
                }
                _ => {}
            }

            // Refuse cases: NoCoverage is sound; nothing to diff against Node.
            let sem_trace = match sem {
                SemOutcome::Trace(t) => t,
                SemOutcome::NoCoverage { .. } => {
                    refused += 1;
                    continue;
                }
            };

            // ParseSyntaxError cases: require byte-for-byte trace equality with
            // the real Node driver (which raises SyntaxError at parse).
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

    eprintln!(
        "== pinned divergences: {equal} parse-SyntaxError traces node-equal, {refused} sound refusals =="
    );
    assert!(
        failures.is_empty(),
        "pinned divergence failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
