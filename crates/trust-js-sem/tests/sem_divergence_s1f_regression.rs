// Regression pins for the 6 sem-divergent runs (3 files x bare/strict) the
// recorded calibration-s1f gate found (build/js262/calibration-s1f-gate/
// sem_divergences.jsonl). All share ONE root cause: the newly-added
// regex-literal lexer decided the regex-vs-division goal from a single-token
// history heuristic, which cannot classify a `/` after `}` — an object-literal
// or function-EXPRESSION `}` is followed by DIVISION, a block / function-
// DECLARATION `}` by a regex — nor the contextual `of` (a division operand
// identifier vs the for-of operator). Every one emitted a spurious SyntaxError
// (the mis-lexed regex ran to a line terminator) where both engines complete
// normally.
//
// The fix drives the goal exactly the way a real engine's tokenizer does: a
// bracket-context stack (an acorn-style token-context state machine) in the
// lexer that tracks operand-vs-operator position through braces, parens and
// function/class bodies. See crates/trust-js-sem/src/lexer.rs (`update_context`,
// `brace_is_block`, the `Ctx`/`PrevType` types).
//
// Disposition per case:
//   * Cover  — the disambiguation lets the program complete; sem must emit a
//     trace byte-for-byte equal to the Node driver's (a wrong trace is
//     gate-fatal).
//   * Refuse — the disambiguation is now correct (a division, not a spurious
//     regex/SyntaxError), but the division coerces a bare Function object to a
//     number, which needs `Function.prototype.toString` — an intrinsic sem
//     does not model. So sem SOUNDLY refuses (NoCoverage) instead of the old
//     WRONG SyntaxError. That is the bar: spec-exact OR a sound refusal, never
//     a wrong trace. (`S11.5.2_A3_T1.5.js` divides `{} / function…` and so
//     falls here; the other two pinned files complete.)
//
// The plain inline tests reduce the disambiguation to boolean-valued /
// refusal-valued cases runnable without Node; the env-gated `..._vs_node` test
// runs the exact pinned files (BOTH modes) AND an adversarial division-vs-regex
// battery through the Node trace driver, requiring trace-equality for Cover
// cases and a sound refusal for Refuse cases.
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
    /// Completes: sem must emit a trace byte-for-byte equal to Node's.
    Cover,
    /// The lex is correct (division), but evaluation reaches an unmodeled
    /// intrinsic (`Function.prototype.toString`) — sem SOUNDLY refuses
    /// (NoCoverage), never a wrong SyntaxError.
    Refuse,
}
use Disp::{Cover, Refuse};

/// The three pinned corpus files (each expands to bare + strict).
const PINS: &[(&str, Disp)] = &[
    ("test/language/expressions/division/S11.5.2_A2.2_T1.js", Cover),
    // Divides `{} / function(){…}` and `function(){…} / {}`: the function
    // operand's ToNumber needs Function.prototype.toString → sound refusal.
    ("test/language/expressions/division/S11.5.2_A3_T1.5.js", Refuse),
    ("test/language/expressions/division/no-magic-asi.js", Cover),
];

/// The adversarial division-vs-regex battery. Each Cover body prints its
/// result, so a mis-classified `/` would diverge either as a spurious
/// SyntaxError (a mis-lexed regex running to EOL) or as a different printed
/// value. Refuse cases exercise the same disambiguation but hit the
/// Function.prototype.toString gap and must SOUNDLY refuse.
fn adversarial() -> Vec<(&'static str, Disp, &'static str)> {
    vec![
        // -- object-literal `}` in expression position => DIVISION -----------
        ("obj-div-nan", Cover, "console.log(({a:1} / 1));"),
        ("obj-valueof-div", Cover, "console.log(({valueOf: function(){return 6}} / 2));"),
        ("obj-in-parens-div", Cover, "console.log(({} / 1));"),
        ("obj-rhs-div", Cover, "console.log((1 / {toString: function(){return 2}}));"),
        (
            "obj-two-methods-div",
            Cover,
            "console.log(({valueOf: function(){return 1}, toString: function(){return 0}} / 1));",
        ),
        // -- function-EXPRESSION body `}` => DIVISION (sound refusal: the ------
        //    function's ToNumber needs Function.prototype.toString) -----------
        ("fnexpr-div", Refuse, "console.log((function(){return 1} / {}));"),
        ("fnexpr-in-call-div", Refuse, "console.log(isNaN(function(){return 1} / {}));"),
        (
            "fnexpr-both-div",
            Refuse,
            "console.log(isNaN(function(){return 1} / function(){return 1}));",
        ),
        // -- array `]`, call `)`, postfix `++` => DIVISION -------------------
        ("array-div", Cover, "console.log([] / 1);"),
        ("array-len-div", Cover, "console.log([1,2,3].length / 3);"),
        ("call-div", Cover, "console.log((function(){return 8})() / 2);"),
        ("postfix-div", Cover, "var x = 6; console.log(x++ / 2, x);"),
        ("chain-div", Cover, "console.log(12 / 2 / 3);"),
        // -- contextual `of` as an operand identifier => DIVISION (no ASI) ---
        ("of-ident-div", Cover, "var instance = 60, of = 6, g = 2; console.log(instance/of/g);"),
        // -- block `}` (statement position) => the next `/` is a REGEX -------
        ("block-then-regex", Cover, "{}\n/x/g;\nconsole.log('block-then-regex-ok');"),
        (
            "block-then-regex-observed",
            Cover,
            "var re; { } re = /ab+c/.test('abbc'); console.log(re);",
        ),
        // -- function-DECLARATION body `}` => REGEX --------------------------
        (
            "fndecl-then-regex",
            Cover,
            "function f(){}\n/x/.test('x');\nconsole.log('fndecl-then-regex-ok');",
        ),
        // -- control-head `)` => a REGEX starts the body ---------------------
        ("if-head-regex", Cover, "if (false) /x/.test('x');\nconsole.log('if-head-ok');"),
        ("while-head-regex", Cover, "while (false) /x/.test('x');\nconsole.log('while-head-ok');"),
        // -- before-expression keywords => REGEX -----------------------------
        ("return-regex", Cover, "function f(){ return /ab/g.test('xabz'); } console.log(f());"),
        ("typeof-regex", Cover, "console.log(typeof /x/);"),
        ("void-regex", Cover, "console.log(void /x/);"),
        ("ternary-regex", Cover, "var b = true; console.log((b ? /a/ : /b/).source);"),
        // -- the for-of operator `of` DOES take a regex operand --------------
        (
            "forof-regex-operand",
            Cover,
            "var s = ''; for (var r of [/a/, /bc/]) s += r.source; console.log(s);",
        ),
        ("forof-string", Cover, "var s = ''; for (var c of 'ab') s += c; console.log(s);"),
        // -- regex whose class hides a `/`, then a real division -------------
        ("class-slash-then-div", Cover, "var r = /[/]/; console.log(r.test('/'), 6 / 2);"),
        // -- leading regex (program start is operand position) ---------------
        ("leading-regex", Cover, "console.log(/x/.test('axb'));"),
        // -- template substitution runs an independent goal ------------------
        ("tmpl-obj-div", Cover, "console.log(`${ ({a:1} / 1) }`);"),
        ("tmpl-regex", Cover, "console.log(`${ /ab/.test('zabz') }`);"),
    ]
}

// ---------------------------------------------------------------------------
// Plain inline tests (no Node): a boolean-/refusal-reduced case per rule.
// ---------------------------------------------------------------------------

/// The `true` boolean completion (a snippet reduced to a single spec-truth). A
/// mis-classified `/` would instead throw a SyntaxError (or a wrong value),
/// never a `true` normal completion.
fn assert_true(src: &str) {
    let c = match evaluate_case(&[], src) {
        SemOutcome::Trace(t) => t.completion,
        SemOutcome::NoCoverage { reason } => panic!("unexpected NoCoverage for {src}: {reason}"),
    };
    assert_eq!(
        c,
        Completion::Normal {
            v: Some(ProjectedValue::Bool { v: true })
        },
        "expected `true` completion for: {src}"
    );
}

/// A SOUND refusal: sem produces NoCoverage — crucially NOT a Trace (which
/// would mean either a wrong SyntaxError, the old bug, or a wrong value).
fn assert_sound_refusal(src: &str) {
    match evaluate_case(&[], src) {
        SemOutcome::NoCoverage { .. } => {}
        SemOutcome::Trace(t) => panic!(
            "expected a sound NoCoverage refusal for {src}, got a trace: {:?}",
            t.completion
        ),
    }
}

#[test]
fn division_after_value_producing_close() {
    // Object literal in expression position: `}` is followed by division.
    assert_true("({valueOf: function(){return 6}} / 2) === 3;");
    assert_true("({} / 1) !== ({} / 1);"); // NaN !== NaN
    assert_true("(1 / {toString: function(){return 2}}) === 0.5;");
    // Array `]`, call `)`, postfix `++`.
    assert_true("([] / 1) === 0;");
    assert_true("([1,2,3].length / 3) === 1;");
    assert_true("((function(){return 8})() / 2) === 4;");
    assert_true("(function(){ var x = 6; return x++ / 2 === 3 && x === 7; })();");
    assert_true("(12 / 2 / 3) === 2;");
    // The contextual `of` used as an operand identifier divides (no ASI).
    assert_true(
        "(function(){ var instance = 60, of = 6, g = 2; return instance/of/g === 5; })();",
    );
    // Function-EXPRESSION body `}` => division (the `function` sits in
    // expression position — after `=`, or inside a call). The lex is now
    // correct (no spurious SyntaxError from a mis-lexed regex); the division's
    // ToNumber(function) then reaches the unmodeled Function.prototype.toString,
    // so sem SOUNDLY refuses rather than emitting a wrong trace.
    assert_sound_refusal("isNaN(function(){return 1} / {});");
    assert_sound_refusal("var q = function(){return 1} / {}; q;");
}

#[test]
fn regex_in_operand_position() {
    // A block `}` (statement position) is followed by a regex-literal start;
    // a mis-lex would make `{}/x/;` a SyntaxError.
    assert_true("(function(){ {}/x/; return true; })();");
    // Function-DECLARATION body `}` => regex.
    assert_true("(function(){ function g(){}\n/x/.test('x'); return true; })();");
    // Control-head `)` => the body statement begins with a regex operand.
    assert_true("(function(){ if (false) /x/.test('x'); return true; })();");
    assert_true("(function(){ while (false) /x/.test('x'); return true; })();");
    // Before-expression keywords.
    assert_true("typeof /x/ === 'object';");
    assert_true("(function(){ return /ab/g.test('xabz'); })();");
    // The for-of operator `of` DOES permit a regex operand.
    assert_true("(function(){ var s=''; for (var r of [/a/,/bc/]) s += r.source; return s === 'abc'; })();");
    // Regex whose class hides `/`, then a real division after the value.
    assert_true("(function(){ var r = /[/]/; return r.test('/') && 6 / 2 === 3; })();");
    // Template substitution runs an independent operand-position goal.
    assert_true("`${ /ab/.test('zabz') }` === 'true';");
    assert_true("`${ ({a:1} / 1) }` === 'NaN';");
}

// ---------------------------------------------------------------------------
// Frontmatter + harness plumbing (shared shape with the corpus runners).
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
// Plain corpus sweep (no Node): each pinned file must match its ruled
// disposition in every applicable mode (never a spurious SyntaxError).
// ---------------------------------------------------------------------------

#[test]
fn pinned_s1f_divergences_local_cover() {
    let Some(corpus) = corpus_root() else {
        eprintln!("SKIP pinned_s1f_divergences_local_cover: corpus not present");
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
            let ok = match (disp, &out) {
                // Cover: a Normal completion (the program runs to the end).
                (Disp::Cover, SemOutcome::Trace(t)) => {
                    matches!(t.completion, Completion::Normal { .. })
                }
                // Refuse: a sound NoCoverage — NOT a (wrong-SyntaxError) trace.
                (Disp::Refuse, SemOutcome::NoCoverage { .. }) => true,
                _ => false,
            };
            if !ok {
                failures.push(format!("{rel} [{mode}]: expected {disp:?}, got {out:?}"));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "pinned s1f local cover ({} of {checked} checks failed):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Env-gated differential vs the Node trace driver.
// ---------------------------------------------------------------------------

/// Run one program through sem + the Node driver, enforcing its disposition.
#[allow(clippy::too_many_arguments)]
fn check_vs_node(
    node: &str,
    driver: &Path,
    tmp: &Path,
    case_no: usize,
    label: &str,
    disp: Disp,
    includes: &[String],
    sem: SemOutcome,
    body: &str,
    mode: &str,
    completion_witness: bool,
    failures: &mut Vec<String>,
    equal: &mut u64,
) {
    let sem_trace = match (disp, sem) {
        (Disp::Cover, SemOutcome::Trace(t)) => t,
        (Disp::Cover, SemOutcome::NoCoverage { reason }) => {
            failures.push(format!("{label}: expected covered trace, got NoCoverage: {reason}"));
            return;
        }
        // A sound refusal: no wrong trace. Nothing to compare against Node.
        (Disp::Refuse, SemOutcome::NoCoverage { .. }) => {
            *equal += 1;
            return;
        }
        (Disp::Refuse, SemOutcome::Trace(t)) => {
            failures.push(format!(
                "{label}: expected a sound refusal, got a trace: {:?}",
                t.completion
            ));
            return;
        }
    };

    let body_path = tmp.join(format!("s1f-{case_no}.body.js"));
    std::fs::write(&body_path, body).expect("write body");
    let manifest = serde_json::json!({
        "completion_witness": completion_witness,
        "includes": includes,
        "source": body_path.display().to_string(),
        "mode": mode,
        "kind": "script",
    });
    let manifest_path = tmp.join(format!("s1f-{case_no}.manifest.json"));
    let mut mf = std::fs::File::create(&manifest_path).expect("create manifest");
    mf.write_all(manifest.to_string().as_bytes())
        .expect("write manifest");
    drop(mf);

    let out = Command::new(node)
        .arg(driver)
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
                "{label}: node trace extraction failed: {e} (stderr: {})",
                String::from_utf8_lossy(&out.stderr)
            ));
            return;
        }
    };
    if traces_equal(&sem_trace, &node_trace) {
        *equal += 1;
    } else {
        failures.push(format!(
            "{label}: WRONG TRACE\n  sem:  {:?}\n  node: {:?}",
            sem_trace.completion, node_trace.completion
        ));
    }
}

#[test]
fn pinned_s1f_divergences_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP pinned_s1f_divergences_vs_node: set TRUST_JS_NODE to run");
        return;
    };
    let driver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs");
    assert!(driver.is_file(), "driver not found at {}", driver.display());

    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();
    let mut equal = 0u64;
    let mut case_no = 0usize;

    // 1) The three pinned corpus files, both applicable modes each.
    if let Some(corpus) = corpus_root() {
        let mut include_cache: std::collections::HashMap<String, String> =
            std::collections::HashMap::new();
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
                check_vs_node(
                    &node,
                    &driver,
                    tmp.path(),
                    case_no,
                    &format!("{rel} [{mode}]"),
                    *disp,
                    &include_paths,
                    sem,
                    &body,
                    mode,
                    false,
                    &mut failures,
                    &mut equal,
                );
            }
        }
    } else {
        eprintln!("(corpus absent: skipping the 3 pinned files, running the battery only)");
    }

    // 2) The adversarial division-vs-regex battery (bare mode, self-contained).
    for (name, disp, body) in adversarial() {
        case_no += 1;
        let sem = evaluate_case(&[], body);
        check_vs_node(
            &node,
            &driver,
            tmp.path(),
            case_no,
            &format!("adversarial/{name}"),
            disp,
            &[],
            sem,
            body,
            "bare",
            true,
            &mut failures,
            &mut equal,
        );
    }

    eprintln!("== s1f division-vs-regex: {equal} node-equal / soundly-refused ==");
    assert!(
        failures.is_empty(),
        "s1f divergence failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
