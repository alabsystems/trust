// Env-gated adversarial + corpus differential for the Symbol (20.4) and Date
// (21.4) surfaces grown onto the reference head: symbol values/coercions/
// registry/well-known identities, symbol-keyed properties and the @@-protocol
// dispatch (@@toPrimitive / @@hasInstance / @@iterator), and the exactly-
// determined Date field/ISO machinery under the driver's pinned clock. Every
// Cover case must be byte-for-byte trace-equal with the Node driver; Refuse
// cases pin the sound NoCoverage behavior. Skips loudly when TRUST_JS_NODE is
// unset.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::BTreeMap;
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

#[derive(Clone, Copy, PartialEq)]
enum Expect {
    Cover,
    Refuse,
}
use Expect::{Cover as C, Refuse as R};

struct Case {
    name: &'static str,
    strict: bool,
    expect: Expect,
    body: &'static str,
}

fn node_bin() -> Option<String> {
    std::env::var("TRUST_JS_NODE").ok()
}

fn driver_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs")
}

fn node_trace_of(
    node: &str,
    driver: &Path,
    tmp: &Path,
    tag: &str,
    body: &str,
    includes: &[String],
    strict: bool,
    witness: bool,
) -> Result<trust_js_trace::ObservableTrace, String> {
    let body_path = tmp.join(format!("{tag}.body.js"));
    std::fs::write(&body_path, body).expect("write body");
    let manifest = serde_json::json!({
        "completion_witness": witness,
        "includes": includes,
        "source": body_path.display().to_string(),
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

#[allow(clippy::too_many_lines)]
fn cases() -> Vec<Case> {
    let mut v = Vec::new();
    let mut c = |name: &'static str, strict: bool, expect: Expect, body: &'static str| {
        v.push(Case { name, strict, expect, body });
    };

    // ---- Symbol values, coercions, registry ------------------------------
    c("sym-typeof", false, C, "console.log(typeof Symbol(), typeof Symbol.iterator);");
    c("sym-description", false, C,
      "console.log(Symbol('x').description, Symbol().description, Symbol(123).description);");
    c("sym-tostring", false, C,
      "console.log(Symbol('z').toString(), String(Symbol('y')), String(Symbol()));");
    c("sym-valueof", false, C,
      "var s = Symbol('v'); console.log(s.valueOf() === s, Object(s).valueOf() === s);");
    c("sym-for-keyfor", false, C,
      "console.log(Symbol.for('k') === Symbol.for('k'), Symbol.keyFor(Symbol.for('m')), Symbol.keyFor(Symbol('z')));");
    c("sym-wellknown-identity", false, C,
      "console.log(Symbol.iterator === Symbol.iterator, typeof Symbol.asyncIterator, Symbol.hasInstance === Symbol.hasInstance);");
    c("sym-project-value", false, C, "console.log(Symbol('desc'), Symbol.iterator, Symbol());");
    c("sym-equality", false, C,
      "var a = Symbol(); var b = Symbol(); console.log(a === a, a === b, a == a, Object(a) == a);");
    c("sym-boolean", false, C, "console.log(!!Symbol(), Symbol() ? 'y' : 'n');");
    c("sym-typeof-object-wrap", false, C, "console.log(typeof Object(Symbol()), Object(Symbol()) instanceof Symbol);");
    c("sym-ctor-props", false, C, "console.log(Symbol.name, Symbol.length, typeof Symbol.prototype);");
    c("sym-to-number-throws", false, C,
      "var t = false; try { Symbol() + 1; } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("sym-to-string-throws", false, C,
      "var t = false; try { `${Symbol()}`; } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("sym-new-throws", false, C,
      "var t = false; try { new Symbol(); } catch (e) { t = e instanceof TypeError; } console.log(t);");
    c("sym-desc-getter-this", false, C,
      "var t = false; try { Object.getOwnPropertyDescriptor(Symbol.prototype, 'description').get.call(5); } catch (e) { t = e instanceof TypeError; } console.log(t);");

    // ---- Symbol-keyed properties -----------------------------------------
    c("sym-keyed-get-set", false, C,
      "var s = Symbol('k'); var o = {}; o[s] = 42; console.log(o[s], s in o, o[Symbol()]);");
    c("sym-keyed-literal", false, C,
      "var s = Symbol(); var o = { [s]: 7, a: 1 }; console.log(o[s], o.a, Object.getOwnPropertySymbols(o).length);");
    c("sym-keyed-projection", false, C,
      "var s = Symbol('d'); var o = { a: 1 }; o[s] = 9; console.log(o);");
    c("sym-keyed-delete", false, C,
      "var s = Symbol(); var o = {}; o[s] = 1; var d = delete o[s]; console.log(d, s in o);");
    c("sym-keyed-defineproperty", false, C,
      "var s = Symbol('p'); var o = {}; Object.defineProperty(o, s, { value: 5, enumerable: false });\n\
       var desc = Object.getOwnPropertyDescriptor(o, s);\n\
       console.log(o[s], desc.enumerable, desc.writable, Object.keys(o).length);");
    c("sym-getownpropertysymbols-order", false, C,
      "var a = Symbol('a'); var b = Symbol('b'); var o = {}; o[a] = 1; o[b] = 2;\n\
       var syms = Object.getOwnPropertySymbols(o); console.log(syms.length, syms[0] === a, syms[1] === b);");
    c("sym-not-in-keys", false, C,
      "var s = Symbol(); var o = { x: 1 }; o[s] = 2; var ks = []; for (var k in o) ks.push(k);\n\
       console.log(ks, Object.keys(o), Object.getOwnPropertyNames(o));");

    // ---- @@-protocol dispatch --------------------------------------------
    c("sym-toprimitive", false, C,
      "var o = { [Symbol.toPrimitive](h) { return h === 'number' ? 42 : h; } };\n\
       console.log(+o, `${o}`, o + '');");
    c("sym-hasinstance-override", false, C,
      "function F() {} F[Symbol.hasInstance] = function () { return true; };\n\
       console.log({} instanceof F, 5 instanceof F);");
    c("sym-hasinstance-default", false, C,
      "function F() {} var f = new F(); console.log(f instanceof F, ({}) instanceof F);");
    c("sym-array-iterator-identity", false, C,
      "console.log(typeof [][Symbol.iterator], [][Symbol.iterator] === Array.prototype.values);");
    c("sym-object-tostring-tag", false, C,
      "var o = {}; console.log(Object.prototype.toString.call(o));");

    // String.prototype[@@iterator] (22.1.3.35) is modeled: a code-point
    // iterator method. (Its identity/behavior is exercised in
    // iterator_corpus_sweep; here just pin typeof + name.)
    c("sym-string-iterator-modeled", false, C,
      "var f = ''[Symbol.iterator]; console.log(typeof f, f.name, f.length);");

    // ---- Symbol refusals --------------------------------------------------
    c("sym-dispose-refuses", false, R, "Symbol.dispose;");
    c("sym-user-iterator-refuses", false, R,
      "var o = { [Symbol.iterator]() { return { next() { return { done: true }; } }; } };\n\
       for (var x of o) {} console.log('never');");
    c("sym-class-key-refuses", false, R, "class A { [Symbol.iterator]() {} }");

    // ---- Date construction + fields --------------------------------------
    c("date-utc-fields", false, C,
      "var d = new Date(Date.UTC(2023, 10, 15, 12, 30, 45, 123));\n\
       console.log(d.getUTCFullYear(), d.getUTCMonth(), d.getUTCDate(), d.getUTCDay(),\n\
       d.getUTCHours(), d.getUTCMinutes(), d.getUTCSeconds(), d.getUTCMilliseconds());");
    c("date-local-equals-utc", false, C,
      "var d = new Date(2023, 10, 15, 12, 30, 45, 123);\n\
       console.log(d.getFullYear(), d.getMonth(), d.getDate(), d.getHours(), d.getMinutes(), d.getSeconds(), d.getMilliseconds(), d.getTimezoneOffset());");
    c("date-valueof", false, C,
      "var d = new Date(Date.UTC(2023, 10, 15, 12, 30, 45, 123));\n\
       console.log(d.valueOf(), d.getTime(), +d);");
    c("date-iso", false, C,
      "console.log(new Date(Date.UTC(2023, 10, 15, 12, 30, 45, 123)).toISOString(), new Date(0).toISOString());");
    c("date-iso-negyear", false, C,
      "console.log(new Date(Date.UTC(-1, 0, 1)).toISOString());");
    c("date-rollover", false, C,
      "console.log(new Date(2023, 12, 1).toISOString(), new Date(2023, 0, 32).toISOString());");
    c("date-two-arg", false, C, "console.log(new Date(2023, 0).toISOString());");
    c("date-onearg-num", false, C, "console.log(new Date(1700000000000).toISOString());");
    c("date-onearg-str", false, C, "console.log(new Date('2023-11-15').toISOString());");
    c("date-copy", false, C,
      "var a = new Date(Date.UTC(2020, 5, 1)); var b = new Date(a); console.log(a.getTime() === b.getTime());");
    c("date-utc-static", false, C,
      "console.log(Date.UTC(2023, 10, 15, 12, 30, 45, 123), Date.UTC(2023), Date.UTC(2023, 0, 1));");
    c("date-parse-iso", false, C,
      "console.log(Date.parse('2023-11-15T12:30:45.123Z'), Date.parse('2023-11-15'), Date.parse('2023'), Date.parse('2023-11'));");
    c("date-parse-tz", false, C,
      "console.log(Date.parse('2023-11-15T12:30:45+05:00'), Date.parse('2023-11-15T12:30'));");
    c("date-nan", false, C,
      "console.log(new Date(NaN).getTime(), new Date(NaN).getUTCFullYear());");
    c("date-tojson", false, C,
      "console.log(new Date(Date.UTC(2023, 5, 15, 10, 20, 30, 40)).toJSON());");
    c("date-setters", false, C,
      "var d = new Date(Date.UTC(2020, 0, 1));\n\
       d.setUTCFullYear(2021); console.log(d.toISOString());\n\
       d.setUTCMonth(5); console.log(d.toISOString());\n\
       d.setUTCHours(13, 14, 15, 16); console.log(d.toISOString());");
    c("date-settime", false, C,
      "var d = new Date(0); d.setTime(Date.UTC(2000, 0, 1)); console.log(d.toISOString());");
    c("date-toprimitive-number", false, C,
      "var d = new Date(Date.UTC(2000, 0, 1)); console.log(d[Symbol.toPrimitive]('number'));");
    c("date-tostring-tag", false, C,
      "console.log(Object.prototype.toString.call(new Date(0)));");
    c("date-clock-ticks", false, C,
      "console.log(Date.now(), Date.now(), new Date().getTime());");
    c("date-typeof-now", false, C, "console.log(typeof Date.now(), typeof new Date());");
    c("date-instanceof", false, C,
      "console.log(new Date(0) instanceof Date, new Date(0) instanceof Object);");
    c("date-iso-rangeerror", false, C,
      "var t = false; try { new Date(NaN).toISOString(); } catch (e) { t = e instanceof RangeError; } console.log(t);");

    // ---- Date refusals ----------------------------------------------------
    c("date-tostring-refuses", false, R, "new Date(0).toString();");
    c("date-called-as-fn-refuses", false, R, "Date();");
    c("date-datestring-refuses", false, R, "new Date(0).toDateString();");
    c("date-parse-noniso-refuses", false, R, "Date.parse('November 15, 2023');");
    c("date-str-garbage-refuses", false, R, "new Date('garbage').getTime();");

    v
}

#[test]
#[allow(clippy::too_many_lines)]
fn symbol_date_adversarial_vs_node() {
    let Some(node) = node_bin() else {
        eprintln!("SKIP symbol_date_adversarial_vs_node: set TRUST_JS_NODE to run");
        return;
    };
    let driver = driver_path();
    assert!(driver.is_file(), "driver not found at {}", driver.display());
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();

    for (ci, case) in cases().iter().enumerate() {
        let sem_body = if case.strict {
            format!("\"use strict\";\n{}", case.body)
        } else {
            case.body.to_string()
        };
        let sem = evaluate_case(&[], &sem_body);
        let sem_trace = match (sem, case.expect) {
            (SemOutcome::NoCoverage { .. }, Expect::Refuse) => continue,
            (SemOutcome::NoCoverage { reason }, Expect::Cover) => {
                failures.push(format!("{}: unexpected NoCoverage: {reason}", case.name));
                continue;
            }
            (SemOutcome::Trace(_), Expect::Refuse) => {
                failures.push(format!("{}: expected refusal but produced a trace", case.name));
                continue;
            }
            (SemOutcome::Trace(t), Expect::Cover) => t,
        };
        let node_trace = match node_trace_of(
            &node,
            &driver,
            tmp.path(),
            &format!("adv-{ci}"),
            case.body,
            &[],
            case.strict,
            true,
        ) {
            Ok(t) => t,
            Err(e) => {
                failures.push(format!("{}: {e}", case.name));
                continue;
            }
        };
        if !traces_equal(&sem_trace, &node_trace) {
            failures.push(format!(
                "{}: DIVERGENCE: {}",
                case.name,
                explain_divergence(&sem_trace, &node_trace).unwrap_or_else(|| "unlocalized".into())
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "symbol/date adversarial failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Corpus sweep over the Symbol / Date directories.
// ---------------------------------------------------------------------------

const SWEEP_DIRS: &[(&str, usize)] = &[
    ("test/built-ins/Symbol", 400),
    ("test/built-ins/Date/prototype/constructor", 20),
    ("test/built-ins/Date/prototype/getUTCMinutes", 30),
    ("test/built-ins/Date/prototype/getUTCSeconds", 30),
    ("test/built-ins/Date/prototype/getUTCDay", 30),
    ("test/built-ins/Date/prototype/getUTCMilliseconds", 30),
    ("test/built-ins/Date/prototype/setUTCFullYear", 40),
    ("test/built-ins/Date/prototype/setUTCHours", 40),
    ("test/built-ins/Date", 40),
    ("test/built-ins/Date/prototype/getUTCFullYear", 40),
    ("test/built-ins/Date/prototype/getUTCMonth", 40),
    ("test/built-ins/Date/prototype/getUTCDate", 40),
    ("test/built-ins/Date/prototype/getUTCHours", 40),
    ("test/built-ins/Date/prototype/valueOf", 40),
    ("test/built-ins/Date/prototype/getTime", 40),
    ("test/built-ins/Date/prototype/toISOString", 60),
    ("test/built-ins/Date/prototype/toJSON", 40),
    ("test/built-ins/Date/prototype/setTime", 40),
    ("test/built-ins/Date/prototype/getTimezoneOffset", 30),
    ("test/built-ins/Date/prototype/Symbol.toPrimitive", 30),
    ("test/built-ins/Date/now", 30),
    ("test/built-ins/Date/UTC", 100),
    ("test/built-ins/Date/parse", 120),
    ("test/built-ins/Date/prototype/setUTCMonth", 40),
    ("test/built-ins/Date/prototype/setUTCDate", 40),
    ("test/built-ins/Date/prototype/setUTCMinutes", 40),
    ("test/built-ins/Date/prototype/setUTCSeconds", 40),
    ("test/built-ins/Date/prototype/setUTCMilliseconds", 40),
    ("test/built-ins/Date/prototype/valueOf", 30),
    ("test/built-ins/Date/proto", 20),
    ("test/built-ins/Date/name", 10),
    ("test/built-ins/Date/length", 10),
    ("test/built-ins/Array/prototype/Symbol.iterator", 20),
    ("test/language/expressions/instanceof", 40),
    ("test/language/expressions/typeof", 30),
];

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
                    } else {
                        break;
                    }
                }
            }
        } else if let Some(rest) = t.strip_prefix("flags:") {
            if let Some(inner) = rest.trim().strip_prefix('[') {
                flags.extend(
                    inner
                        .trim_end_matches(']')
                        .split(',')
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty()),
                );
            }
        }
    }
    Frontmatter { includes, flags }
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

#[test]
#[allow(clippy::too_many_lines)]
fn symbol_date_corpus_vs_node() {
    let Some(node) = node_bin() else {
        eprintln!("SKIP symbol_date_corpus_vs_node: set TRUST_JS_NODE (and optionally TRUST_JS262_CORPUS) to run");
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
    let (mut covered, mut refused, mut equal) = (0u64, 0u64, 0u64);
    let mut per_dir: BTreeMap<&str, (u64, u64)> = BTreeMap::new();
    let mut include_cache: BTreeMap<String, String> = BTreeMap::new();
    let mut reasons: BTreeMap<String, (u64, String)> = BTreeMap::new();
    let mut case_no = 0usize;

    for (dir, cap) in SWEEP_DIRS {
        for path in collect_js_files(&corpus.join(dir), *cap) {
            let Ok(body) = std::fs::read_to_string(&path) else { continue };
            let fm = parse_frontmatter(&body);
            if fm.flags.iter().any(|f| f == "async" || f == "module" || f == "CanBlockIsRequired") {
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
                vec!["assert.js".into(), "sta.js".into()]
            };
            include_names.extend(fm.includes.iter().cloned());
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
                let sem_body = if strict { format!("\"use strict\";\n{body}") } else { body.clone() };
                let inc_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();
                let sem_trace = match evaluate_case_opts(&inc_refs, &sem_body, false) {
                    SemOutcome::Trace(t) => t,
                    SemOutcome::NoCoverage { reason } => {
                        refused += 1;
                        per_dir.entry(dir).or_default().1 += 1;
                        reasons.entry(reason).or_insert_with(|| (0, rel.clone())).0 += 1;
                        continue;
                    }
                };
                covered += 1;
                per_dir.entry(dir).or_default().0 += 1;
                let node_trace = match node_trace_of(
                    &node, &driver, tmp.path(), &format!("case-{case_no}"), &body, &include_paths, strict, false,
                ) {
                    Ok(t) => t,
                    Err(e) => {
                        failures.push(format!("{rel} [{}]: {e}", if strict { "strict" } else { "bare" }));
                        continue;
                    }
                };
                if traces_equal(&sem_trace, &node_trace) {
                    equal += 1;
                } else {
                    failures.push(format!(
                        "{rel} [{}]: WRONG TRACE: {}",
                        if strict { "strict" } else { "bare" },
                        explain_divergence(&sem_trace, &node_trace).unwrap_or_else(|| "unlocalized".into())
                    ));
                }
            }
        }
    }

    eprintln!("== symbol/date corpus: covered {covered} (equal {equal}) / refused {refused} ==");
    for (dir, (cc, rr)) in &per_dir {
        eprintln!("  {dir}: covered {cc} refused {rr}");
    }
    let mut rs: Vec<(u64, String, String)> =
        reasons.into_iter().map(|(k, (n, s))| (n, k, s)).collect();
    rs.sort_by(|a, b| b.0.cmp(&a.0));
    eprintln!("== top refusal reasons ==");
    for (n, reason, sample) in rs.iter().take(25) {
        eprintln!("  {n} x {reason} (e.g. {sample})");
    }
    assert!(
        failures.is_empty(),
        "symbol/date corpus failures (wrong trace is never acceptable) ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
