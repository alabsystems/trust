// Env-gated adversarial differential for the RegExp surface (22.2): literal
// parsing (source/flags/toString), exec/test result shape + lastIndex, the
// global/sticky loops, the @@match/@@matchAll/@@replace/@@search/@@split
// protocols and the String.prototype methods that dispatch through them, the
// $-substitution table, named groups, matchAll's %RegExpStringIterator%, and
// the flag accessors. Cover cases must be byte-for-byte trace-equal with the
// real Node driver; Refuse cases pin the sound NoCoverage behavior. Skips
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
    expect: Expect,
    body: &'static str,
}

const C: Expect = Expect::Cover;
const R: Expect = Expect::Refuse;

#[allow(clippy::too_many_lines)]
fn cases() -> Vec<Case> {
    let mut v = Vec::new();
    let mut c = |name: &'static str, expect: Expect, body: &'static str| {
        v.push(Case { name, expect, body });
    };

    // ---- literals: source / flags / toString -----------------------------
    c("lit-source-flags", C, "console.log(/abc/gi.source, /abc/gi.flags);");
    c("lit-escape-slash", C, "console.log(/a\\/b/.source, String(/a\\/b/g));");
    c("lit-class-slash", C, "console.log(/[/]/.source, /[a/b]/.source);");
    c("lit-empty-source", C, "console.log(new RegExp('').source, new RegExp('').toString());");
    c("lit-flags-order", C, "console.log(new RegExp('a', 'yg').flags, String(new RegExp('a', 'yig')));");
    c("lit-tostring", C, "console.log(/foo/.toString(), /bar/gimsuy.toString());");
    c("ctor-escape-slash", C, "console.log(new RegExp('a/b').source, new RegExp('\\n').source);");
    c("lit-object-projection", C, "console.log(/abc/g);");

    // ---- flag accessors ---------------------------------------------------
    c("flags-all", C,
      "var r = /a/dgimsuy; console.log(r.hasIndices, r.global, r.ignoreCase, r.multiline, r.dotAll, r.unicode, r.sticky);");
    c("flags-v-mode", C, "var r = /a/v; console.log(r.unicodeSets, r.unicode, r.flags);");
    c("flags-proto-source", C, "console.log(RegExp.prototype.source, RegExp.prototype.flags);");
    c("flags-on-nonregexp-throws", C,
      "var t = false; try { Object.getOwnPropertyDescriptor(RegExp.prototype, 'global').get.call({}); } catch (e) { t = e instanceof TypeError; } console.log(t);");

    // ---- exec / test ------------------------------------------------------
    c("exec-basic-shape", C, "var m = /(a)(b)/.exec('xaby'); console.log(m);");
    c("exec-no-match", C, "console.log(/z/.exec('abc'));");
    c("exec-named-groups", C, "var m = /(?<a>x)(?<b>y)/.exec('xy'); console.log(m, m.groups.a, m.groups.b);");
    c("exec-optional-capture", C, "var m = /(a)(b)?/.exec('a'); console.log(m[1], m[2], m.length);");
    c("test-basic", C, "console.log(/\\d+/.test('a12'), /\\d+/.test('abc'));");
    c("exec-lastindex-global", C,
      "var r = /a/g; var out = []; out.push(r.lastIndex); r.exec('xax'); out.push(r.lastIndex); r.exec('xax'); out.push(r.lastIndex); console.log(out);");
    c("exec-sticky", C,
      "var r = /a/y; r.lastIndex = 1; console.log(r.exec('xax') && r.exec('xax').index, r.lastIndex);");
    c("exec-lastindex-reset-onfail", C,
      "var r = /a/g; r.lastIndex = 5; var m = r.exec('ab'); console.log(m, r.lastIndex);");
    c("exec-hasindices", C, "var m = /(?<yr>\\d+)/d.exec('2024'); console.log(m.indices, m.indices.groups);");

    // ---- String.prototype.match ------------------------------------------
    c("match-nonglobal", C, "console.log('hello'.match(/l/));");
    c("match-global", C, "console.log('a1b2c3'.match(/\\d/g));");
    c("match-global-nomatch", C, "console.log('abc'.match(/\\d/g));");
    c("match-string-arg", C, "console.log('a.b.c'.match('.'));");
    c("match-empty-global", C, "console.log('abc'.match(/x*/g));");

    // ---- String.prototype.search -----------------------------------------
    c("search-found", C, "console.log('hello'.search(/l/), 'hello'.search(/z/));");
    c("search-string-arg", C, "console.log('abc'.search('b'));");

    // ---- String.prototype.replace (regexp) -------------------------------
    c("replace-dollar-table", C,
      "console.log('abcabc'.replace(/(b)/g, '[$1-$&-$`-$\\'-$$]'));");
    c("replace-named", C,
      "console.log('2023-01-15'.replace(/(?<y>\\d{4})-(?<m>\\d{2})-(?<d>\\d{2})/, '$<d>/$<m>/$<y>'));");
    c("replace-function", C, "console.log('aaa'.replace(/a/g, function (m, i) { return i; }));");
    c("replace-function-captures", C,
      "console.log('a1b2'.replace(/([a-z])(\\d)/g, function (m, p1, p2, off) { return p2 + p1 + ':' + off; }));");
    c("replace-nonglobal", C, "console.log('aXbXc'.replace(/X/, '-'));");
    c("replace-nn-capture", C, "console.log('abc'.replace(/(a)(b)(c)/, '$3$2$1'));");
    c("replace-string-search", C, "console.log('a.b'.replace('.', '!'));");

    // ---- String.prototype.replaceAll -------------------------------------
    c("replaceall-string", C, "console.log('a-b-c'.replaceAll('-', '+'));");
    c("replaceall-empty", C, "console.log('xyz'.replaceAll('', '.'));");
    c("replaceall-regexp-global", C, "console.log('a1b2'.replaceAll(/\\d/g, '#'));");
    c("replaceall-nonglobal-throws", C,
      "var t = false; try { 'ab'.replaceAll(/a/, 'x'); } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("replaceall-function", C, "console.log('a.b.c'.replaceAll('.', function (m, i) { return i; }));");

    // ---- String.prototype.split (regexp) ---------------------------------
    c("split-basic", C, "console.log('a,b;c'.split(/[,;]/));");
    c("split-captures", C, "console.log('a1b2c'.split(/(\\d)/));");
    c("split-limit", C, "console.log('a,b,c,d'.split(/,/, 2));");
    c("split-empty-string", C, "console.log(''.split(/x/), ''.split(/(?:)/));");
    c("split-string-sep", C, "console.log('a-b-c'.split('-'));");
    c("split-empty-regexp", C, "console.log('abc'.split(/(?:)/));");

    // ---- matchAll + RegExpStringIterator ---------------------------------
    c("matchall-collect", C,
      "var out = []; for (var m of 'a1b2'.matchAll(/(\\d)/g)) out.push(m[0] + ':' + m.index); console.log(out);");
    c("matchall-forof", C,
      "var out = []; for (var m of 'x9y8'.matchAll(/\\d/g)) out.push(m[0]); console.log(out);");
    c("matchall-next", C,
      "var it = 'ab'.matchAll(/[a-z]/g); var a = it.next(); var b = it.next(); var c = it.next(); console.log(a.value[0], b.value[0], c.done);");
    c("matchall-regexp-receiver", C,
      "var n = 0; for (var m of 'aXbX'.matchAll(/X/g)) n++; console.log(n);");
    c("matchall-nonglobal-throws", C,
      "var t = false; try { 'ab'.matchAll(/a/); } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("matchall-object-print", C, "console.log('a'.matchAll(/a/g));");

    // ---- constructor forms ------------------------------------------------
    c("ctor-from-regexp", C, "var a = /abc/gi; var b = new RegExp(a); console.log(b.source, b.flags, b === a);");
    c("ctor-from-regexp-newflags", C, "var b = new RegExp(/abc/gi, 'm'); console.log(b.source, b.flags);");
    c("ctor-call-passthrough", C, "var a = /x/g; console.log(RegExp(a) === a, RegExp(a, 'i') === a);");
    c("ctor-instanceof", C, "console.log(/a/ instanceof RegExp, new RegExp('a') instanceof RegExp);");
    c("ctor-syntaxerror", C,
      "var t = false; try { new RegExp('('); } catch (e) { t = e instanceof SyntaxError; } console.log(t);");
    c("ctor-bad-flags", C,
      "var t = false; try { new RegExp('a', 'q'); } catch (e) { t = e instanceof SyntaxError; } console.log(t);");
    c("ctor-dup-flags", C,
      "var t = false; try { new RegExp('a', 'gg'); } catch (e) { t = e instanceof SyntaxError; } console.log(t);");

    // ---- @@-protocol identity --------------------------------------------
    c("proto-species", C, "console.log(RegExp[Symbol.species] === RegExp);");
    c("proto-has-methods", C,
      "console.log(typeof RegExp.prototype.exec, typeof RegExp.prototype[Symbol.replace], typeof RegExp.prototype[Symbol.matchAll]);");
    c("regexp-tag", C, "console.log(Object.prototype.toString.call(/a/));");

    // ---- unicode ----------------------------------------------------------
    c("unicode-match", C, "console.log('a\\u{1f600}b'.match(/./gu).length);");
    c("unicode-exec-index", C, "var m = /b/u.exec('\\u{1f600}b'); console.log(m.index);");

    // ---- refusals: sound NoCoverage --------------------------------------
    // Annex-B-only literal constructs refuse at parse (never a wrong trace).
    c("refuse-annexb-quantifier", R, "var r = /a{/; console.log(r.source);");
    c("refuse-annexb-lone-bracket", R, "var r = /]/; r.test('x');");
    // ToLowerCase beyond ASCII is already refused; a case-insensitive unicode
    // match through a modeled feature stays covered — not asserted here.

    v
}

#[test]
#[allow(clippy::too_many_lines)]
fn regexp_differential_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP regexp_differential_vs_node: set TRUST_JS_NODE to a node binary to run");
        return;
    };
    let driver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs");
    assert!(driver.is_file(), "driver not found at {}", driver.display());

    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();

    for (ci, case) in cases().iter().enumerate() {
        let sem = evaluate_case(&[], case.body);
        let sem_trace = match (sem, case.expect) {
            (SemOutcome::NoCoverage { reason }, Expect::Refuse) => {
                eprintln!("REFUSES (as pinned) {}: {reason}", case.name);
                continue;
            }
            (SemOutcome::NoCoverage { reason }, Expect::Cover) => {
                failures.push(format!("{}: unexpected NoCoverage: {reason}", case.name));
                continue;
            }
            (SemOutcome::Trace(_), Expect::Refuse) => {
                failures.push(format!(
                    "{}: expected a sound refusal but produced a trace",
                    case.name
                ));
                continue;
            }
            (SemOutcome::Trace(t), Expect::Cover) => t,
        };

        let body_path = tmp.path().join(format!("re-{ci}.body.js"));
        std::fs::write(&body_path, case.body).expect("write body");
        let manifest = serde_json::json!({
            "completion_witness": true,
            "includes": [],
            "source": body_path.display().to_string(),
            "mode": "bare",
            "kind": "script",
        });
        let manifest_path = tmp.path().join(format!("re-{ci}.manifest.json"));
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
        "regexp differential failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
