// Env-gated differential for the standalone iterator OBJECTS: the
// %ArrayIteratorPrototype% (Array + TypedArray values/keys/entries),
// %StringIteratorPrototype% (String[@@iterator] by code point), the shared
// %IteratorPrototype% self-return, and String.prototype.matchAll →
// %RegExpStringIterator%. Two arbiters:
//   * `iterator_adversarial_vs_node` — hand-written minis (values/keys/entries
//     sequencing, next-after-done, live-length, surrogate-pair code points,
//     for-of over .entries(), patched-next OBSERVED, @@toStringTag reads) run
//     vs the real Node driver, each pinned Cover (byte-equal) or Refuse (sound
//     NoCoverage — a tampered fast path must refuse, never emit a wrong trace).
//   * `iterator_corpus_sweep_vs_node` — an UNCAPPED sweep of every case under
//     test/built-ins/{Array,String,TypedArray,Map,Set} iterator dirs through
//     BOTH heads. The bar: ZERO wrong traces and ZERO panics; an unmodeled
//     case (e.g. Map/Set, which the value model does not implement) is a sound
//     NoCoverage refusal, always acceptable.
// Both skip loudly when TRUST_JS_NODE is unset.
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

const SWEEP_DIRS: &[&str] = &[
    // Object.prototype.toString exercises the shared @@toStringTag data-read
    // path (spec-pinned intrinsic tags + user overrides on wrapper prototypes).
    "test/built-ins/Object/prototype/toString",
    "test/built-ins/Array/prototype/values",
    "test/built-ins/Array/prototype/keys",
    "test/built-ins/Array/prototype/entries",
    "test/built-ins/Array/prototype/Symbol.iterator",
    "test/built-ins/ArrayIteratorPrototype",
    "test/built-ins/String/prototype/Symbol.iterator",
    "test/built-ins/String/prototype/matchAll",
    "test/built-ins/StringIteratorPrototype",
    "test/built-ins/IteratorPrototype",
    "test/built-ins/TypedArray/prototype/values",
    "test/built-ins/TypedArray/prototype/keys",
    "test/built-ins/TypedArray/prototype/entries",
    "test/built-ins/TypedArray/prototype/Symbol.iterator",
    "test/built-ins/Map/prototype/entries",
    "test/built-ins/Map/prototype/keys",
    "test/built-ins/Map/prototype/values",
    "test/built-ins/MapIteratorPrototype",
    "test/built-ins/Set/prototype/entries",
    "test/built-ins/Set/prototype/keys",
    "test/built-ins/Set/prototype/values",
    "test/built-ins/SetIteratorPrototype",
];

// ---------------------------------------------------------------------------
// Shared: node driver invocation.
// ---------------------------------------------------------------------------

fn driver_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs")
}

fn run_node(
    node: &str,
    driver: &Path,
    tmp: &Path,
    tag: &str,
    body: &str,
    include_paths: &[String],
    strict: bool,
    completion_witness: bool,
) -> std::process::Output {
    let body_path = tmp.join(format!("{tag}.body.js"));
    std::fs::write(&body_path, body).expect("write body");
    let manifest = serde_json::json!({
        "completion_witness": completion_witness,
        "includes": include_paths,
        "source": body_path.display().to_string(),
        "mode": if strict { "strict" } else { "bare" },
        "kind": "script",
    });
    let manifest_path = tmp.join(format!("{tag}.manifest.json"));
    let mut mf = std::fs::File::create(&manifest_path).expect("create manifest");
    mf.write_all(manifest.to_string().as_bytes())
        .expect("write manifest");
    drop(mf);
    Command::new(node)
        .arg(driver)
        .arg(&manifest_path)
        .env("TZ", "UTC")
        .env("LANG", "C")
        .env("LC_ALL", "C")
        .output()
        .expect("spawn node driver")
}

// ---------------------------------------------------------------------------
// 1. Adversarial minis.
// ---------------------------------------------------------------------------

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

fn cases() -> Vec<Case> {
    let mut v: Vec<Case> = Vec::new();
    let mut c = |name, expect, body| v.push(Case { name, expect, body });

    // ---- Array iterator sequencing --------------------------------------
    c("arr-values-seq", C,
      "var it=[10,20].values(); var a=it.next(),b=it.next(),c=it.next(); console.log(a.value,a.done,b.value,b.done,c.value,c.done);");
    c("arr-keys-seq", C,
      "var it=['a','b','c'].keys(); console.log(it.next().value,it.next().value,it.next().value,it.next().done);");
    c("arr-entries-shape", C,
      "var e=['x','y'].entries(); var p=e.next().value; console.log(p, p.length, e.next().value, e.next().done);");
    c("arr-entries-forof", C,
      "var r=[]; for (var p of ['a','b'].entries()) r.push(p[0]+':'+p[1]); console.log(r);");
    c("arr-next-after-done", C,
      "var it=[1].values(); it.next(); it.next(); console.log(it.next().done, it.next().done);");
    c("arr-live-length-shrink", C,
      "var a=[1,2,3]; var it=a.values(); it.next(); a.length=1; console.log(it.next().done, it.next().done);");
    c("arr-live-length-grow", C,
      "var a=[1]; var it=a.values(); console.log(it.next().value); a.push(2,3); console.log(it.next().value, it.next().value, it.next().done);");
    c("arr-symbol-iterator-is-values", C,
      "console.log(Array.prototype[Symbol.iterator] === Array.prototype.values);");
    c("arr-iter-self-return", C,
      "var it=[1].values(); console.log(it[Symbol.iterator]() === it);");
    c("arr-iter-forof", C,
      "var r=[]; for (var x of [1,2,3].values()) r.push(x*10); console.log(r);");
    c("arr-iter-projects-empty", C, "console.log([1,2].values());");
    c("arr-iter-tag", C,
      "console.log([].values()[Symbol.toStringTag], Object.prototype.toString.call([].keys()));");
    c("arr-iter-own-keys-empty", C,
      "console.log(Object.keys([].values()), Object.getOwnPropertyNames([].entries()).length);");
    c("arr-iter-next-wrong-receiver", C,
      "var t=false; try { [].values().next.call({}); } catch(e){ t = e instanceof TypeError; } console.log(t);");
    c("arr-generic-arraylike", C,
      "var it=Array.prototype.values.call({length:2,0:'p',1:'q'}); console.log(it.next().value,it.next().value,it.next().done);");
    c("arr-values-on-string-object", C,
      "var it=Array.prototype.values.call('ab'); console.log(it.next().value,it.next().value,it.next().done);");

    // ---- patched next OBSERVED -------------------------------------------
    // An explicit .next() call sees a patched %ArrayIteratorPrototype%.next.
    c("arr-patched-next-explicit", C,
      "var it=[1,2].values(); Object.getPrototypeOf(it).next=function(){return {value:99,done:false};};\n\
       console.log(it.next().value, it.next().value);");
    // for-of over a plain array with a patched %ArrayIteratorPrototype%.next:
    // the general protocol would observe it, BUT the frozen driver's own
    // classTag deep-prints via `for (… of INTRINSIC_PROTOS)`, so the patch
    // corrupts the DRIVER's projection (Node reports cls:null for a plain
    // array). The oracle is unreliable → refuse (never a wrong trace).
    c("arr-forof-patched-next-refuses", R,
      "Object.getPrototypeOf([].values()).next=function(){return {value:7,done:true};};\n\
       var r=[]; for (var x of [1,2,3]) r.push(x); console.log(r);");
    // A tampered array-iterator object driven by for-of must refuse.
    c("arr-forof-tampered-iter-refuses", R,
      "var it=[1,2].values(); it.foo=1; var r=[]; for (var x of it) r.push(x); console.log(r);");

    // ---- String iterator -------------------------------------------------
    c("str-iter-codepoints", C,
      "var it='a\\u{1F600}b'[Symbol.iterator](); var x=it.next(),y=it.next(),z=it.next(),w=it.next();\n\
       console.log(x.value, y.value.length, z.value, w.value, w.done);");
    c("str-iter-forof", C,
      "var r=[]; for (var c of 'a\\u{1F600}b'[Symbol.iterator]()) r.push(c); console.log(r.length, r);");
    c("str-raw-forof", C, "var r=[]; for (var c of 'a\\u{1F600}b') r.push(c); console.log(r.length, r);");
    c("str-iter-self-return", C,
      "var s='x'[Symbol.iterator](); console.log(s[Symbol.iterator]() === s);");
    c("str-iter-tag", C,
      "console.log('x'[Symbol.iterator]()[Symbol.toStringTag], Object.prototype.toString.call(''[Symbol.iterator]()));");
    c("str-iter-projects-empty", C, "console.log('ab'[Symbol.iterator]());");
    c("str-iter-next-after-done", C,
      "var it='a'[Symbol.iterator](); it.next(); console.log(it.next().done, it.next().value, it.next().done);");
    c("str-iter-method-props", C,
      "var d=Object.getOwnPropertyDescriptor(String.prototype, Symbol.iterator); console.log(d.value.name, d.value.length, d.writable, d.enumerable, d.configurable);");
    c("str-iter-lone-surrogate", C,
      "var r=[]; for (var c of '\\uD800x'[Symbol.iterator]()) r.push(c.length); console.log(r);");
    c("str-iter-next-wrong-receiver", C,
      "var t=false; try { ''[Symbol.iterator]().next.call([].values()); } catch(e){ t = e instanceof TypeError; } console.log(t);");
    c("str-empty-iter", C,
      "var it=''[Symbol.iterator](); console.log(it.next().done, it.next().value);");
    // Patched String.prototype[@@iterator] observed by a raw for-of → refuse.
    c("str-raw-forof-patched-refuses", R,
      "String.prototype[Symbol.iterator]=function(){return {next:function(){return {done:true};}};};\n\
       var r=[]; for (var c of 'abc') r.push(c); console.log(r);");

    // ---- IteratorPrototype -----------------------------------------------
    c("iterproto-shared", C,
      "var a=Object.getPrototypeOf(Object.getPrototypeOf([].values()));\n\
       var b=Object.getPrototypeOf(Object.getPrototypeOf('x'[Symbol.iterator]()));\n\
       console.log(a === b, typeof a[Symbol.iterator]);");
    c("iterproto-self-return-call", C,
      "var ip=Object.getPrototypeOf(Object.getPrototypeOf([].values()));\n\
       console.log(ip[Symbol.iterator].call(42) === 42);");

    // ---- TypedArray iterator ---------------------------------------------
    c("ta-values", C,
      "var it=new Int8Array([5,6,7]).values(); console.log(it.next().value,it.next().value,it.next().value,it.next().done);");
    c("ta-keys", C,
      "var it=new Uint16Array(3).keys(); console.log(it.next().value,it.next().value,it.next().value,it.next().done);");
    c("ta-entries-forof", C,
      "var r=[]; for (var p of new Int8Array([9,8]).entries()) r.push(p[0]+':'+p[1]); console.log(r);");
    c("ta-iter-is-values", C,
      "console.log(Int8Array.prototype[Symbol.iterator] === Int8Array.prototype.values);");
    c("ta-spread-forof", C,
      "var r=[]; for (var x of new Int8Array([1,2,3])) r.push(x); console.log(r);");

    // ---- Object.prototype.toString @@toStringTag on primitives -----------
    // A user override on a wrapper prototype (data String) is read after
    // ToObject (20.1.3.6 steps 15-16), for BOTH the boxed proto AND the raw
    // primitive.
    c("tostring-bool-override", C,
      "Boolean.prototype[Symbol.toStringTag]='t262';\n\
       console.log(Object.prototype.toString.call(Boolean.prototype), Object.prototype.toString.call(true));");
    c("tostring-num-override", C,
      "Number.prototype[Symbol.toStringTag]='t262';\n\
       console.log(Object.prototype.toString.call(Number.prototype), Object.prototype.toString.call(0));");
    c("tostring-str-override", C,
      "String.prototype[Symbol.toStringTag]='t262';\n\
       console.log(Object.prototype.toString.call(String.prototype), Object.prototype.toString.call(''));");
    c("tostring-sym-override", C,
      "Object.defineProperty(Symbol.prototype, Symbol.toStringTag, {value:'t262'});\n\
       console.log(Object.prototype.toString.call(Symbol.prototype), Object.prototype.toString.call(Symbol()));");
    // Un-overridden primitives keep their builtin/intrinsic tags.
    c("tostring-primitives-default", C,
      "console.log(Object.prototype.toString.call(true), Object.prototype.toString.call(0),\n\
       Object.prototype.toString.call(''), Object.prototype.toString.call(Symbol()),\n\
       Object.prototype.toString.call(1n), Object.prototype.toString.call(undefined),\n\
       Object.prototype.toString.call(null));");

    // ---- matchAll → RegExpStringIterator ---------------------------------
    c("matchall-basic", C,
      "var r=[]; for (var m of 'a1b2c3'.matchAll(/[a-c](\\d)/g)) r.push(m[0]+'/'+m[1]); console.log(r);");
    c("matchall-no-arg-regexp", C,
      "var it='aXbXc'.matchAll('X'); console.log(it.next().value[0], it.next().value.index, it.next().done);");
    c("matchall-nonglobal-throws", C,
      "var t=false; try { 'ab'.matchAll(/a/); } catch(e){ t = e instanceof TypeError; } console.log(t);");
    c("matchall-empty", C,
      "var it='abc'.matchAll(/z/g); console.log(it.next().done);");

    v
}

#[test]
#[allow(clippy::too_many_lines)]
fn iterator_adversarial_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP iterator_adversarial_vs_node: set TRUST_JS_NODE to run");
        return;
    };
    let driver = driver_path();
    assert!(driver.is_file(), "driver not found at {}", driver.display());
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();

    for (ci, case) in cases().iter().enumerate() {
        let sem = evaluate_case_opts(&[], case.body, true);
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
                failures.push(format!("{}: expected a sound refusal but produced a trace", case.name));
                continue;
            }
            (SemOutcome::Trace(t), Expect::Cover) => t,
        };
        let out = run_node(&node, &driver, tmp.path(), &format!("it-{ci}"), case.body, &[], false, true);
        let node_trace = match extract_trace(&out.stdout) {
            Ok(t) => t,
            Err(e) => {
                failures.push(format!(
                    "{}: node trace extraction failed: {e} (stderr: {})",
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
    assert!(
        failures.is_empty(),
        "iterator adversarial failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Diagnostic (no Node): print a histogram of NoCoverage reasons over the
/// sweep dirs, to audit that every refusal is a legitimately-unmodeled surface.
/// Gated on TRUST_JS_IT_REASONS so the normal suite is unaffected.
#[test]
fn iterator_refusal_reasons() {
    if std::env::var("TRUST_JS_IT_REASONS").is_err() {
        eprintln!("SKIP iterator_refusal_reasons: set TRUST_JS_IT_REASONS (+ TRUST_JS262_CORPUS) to run");
        return;
    }
    let corpus = std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string());
    let corpus = PathBuf::from(corpus);
    let assert_src = std::fs::read_to_string(corpus.join("harness/assert.js")).unwrap_or_default();
    let sta_src = std::fs::read_to_string(corpus.join("harness/sta.js")).unwrap_or_default();
    let dirs: Vec<&str> = std::env::var("TRUST_JS_IT_DIRS").ok()
        .map(|s| s.leak() as &str)
        .map_or_else(|| SWEEP_DIRS.to_vec(), |s| s.split(',').map(str::trim).filter(|s| !s.is_empty()).collect());
    let mut hist: std::collections::BTreeMap<String, u32> = std::collections::BTreeMap::new();
    for dir in dirs {
        for path in collect_js_files(&corpus.join(dir), usize::MAX) {
            let Ok(body) = std::fs::read_to_string(&path) else { continue };
            let fm = parse_frontmatter(&body);
            if fm.flags.iter().any(|f| f == "async" || f == "module" || f == "raw") { continue; }
            let mut incs: Vec<&str> = vec![assert_src.as_str(), sta_src.as_str()];
            let extra: Vec<String> = fm.includes.iter().filter_map(|n| std::fs::read_to_string(corpus.join("harness").join(n)).ok()).collect();
            incs.extend(extra.iter().map(String::as_str));
            if let SemOutcome::NoCoverage { reason } = evaluate_case_opts(&incs, &body, false) {
                // Collapse to the reason's leading phrase for grouping.
                let key = reason.split(&['(', ':'][..]).next().unwrap_or(&reason).trim().to_string();
                *hist.entry(key).or_insert(0) += 1;
            }
        }
    }
    let mut rows: Vec<(&String, &u32)> = hist.iter().collect();
    rows.sort_by(|a, b| b.1.cmp(a.1));
    eprintln!("== iterator refusal reason histogram ==");
    for (r, n) in rows {
        eprintln!("{n:5}  {r}");
    }
}

// ---------------------------------------------------------------------------
// 2. Corpus sweep.
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
                includes.extend(inner.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()));
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
                flags.extend(inner.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()));
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
fn iterator_corpus_sweep_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP iterator_corpus_sweep_vs_node: set TRUST_JS_NODE (and optionally \
                   TRUST_JS262_CORPUS / TRUST_JS_IT_SWEEP_CAP / TRUST_JS_IT_DIRS) to run");
        return;
    };
    let corpus = std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string());
    let corpus = PathBuf::from(corpus);
    assert!(corpus.join("harness/assert.js").is_file(), "corpus harness not found under {}", corpus.display());
    let cap = std::env::var("TRUST_JS_IT_SWEEP_CAP").ok().and_then(|s| s.parse::<usize>().ok()).unwrap_or(usize::MAX);
    let driver = driver_path();
    assert!(driver.is_file(), "driver not found at {}", driver.display());

    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();
    let mut panics: Vec<String> = Vec::new();
    let mut covered = 0u64;
    let mut refused = 0u64;
    let mut equal = 0u64;
    let mut include_cache: std::collections::BTreeMap<String, String> = std::collections::BTreeMap::new();

    let override_dirs = std::env::var("TRUST_JS_IT_DIRS").ok();
    let dirs: Vec<&str> = match &override_dirs {
        Some(s) => s.split(',').map(str::trim).filter(|s| !s.is_empty()).collect(),
        None => SWEEP_DIRS.to_vec(),
    };

    let mut case_no = 0usize;
    for dir in dirs {
        let files = collect_js_files(&corpus.join(dir), cap);
        for path in files {
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
                vec!["assert.js".to_string(), "sta.js".to_string()]
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
                let src = include_cache.entry(name.clone()).or_insert_with(|| std::fs::read_to_string(&p).expect("read include"));
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
                let sem = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    evaluate_case_opts(&inc_refs, &sem_body, false)
                })) {
                    Ok(o) => o,
                    Err(_) => {
                        panics.push(format!("{rel} [{}]", if strict { "strict" } else { "bare" }));
                        continue;
                    }
                };
                let sem_trace = match sem {
                    SemOutcome::Trace(t) => t,
                    SemOutcome::NoCoverage { .. } => {
                        refused += 1;
                        continue;
                    }
                };
                covered += 1;
                let mode = if strict { "strict" } else { "bare" };
                let out = run_node(&node, &driver, tmp.path(), &format!("case-{case_no}"), &body, &include_paths, strict, false);
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
                if traces_equal(&sem_trace, &node_trace) {
                    equal += 1;
                } else {
                    failures.push(format!(
                        "{rel} [{mode}]: WRONG TRACE: {}",
                        explain_divergence(&sem_trace, &node_trace).unwrap_or_else(|| "unlocalized".to_string())
                    ));
                }
            }
        }
    }

    eprintln!(
        "== iterator corpus sweep: covered {covered} (equal {equal}) / refused {refused} / panics {} / wrong {} ==",
        panics.len(),
        failures.len()
    );
    assert!(panics.is_empty(), "TOTALITY VIOLATION — {} panic(s):\n{}", panics.len(), panics.join("\n"));
    assert!(
        failures.is_empty(),
        "iterator corpus sweep failures (wrong trace is never acceptable) ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
