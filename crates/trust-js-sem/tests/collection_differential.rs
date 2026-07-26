// Env-gated differential for the keyed collections — Map / Set / WeakMap /
// WeakSet (24) — and the GENERAL iterator protocol over user-defined iterables.
// Two arbiters:
//   * `collection_adversarial_vs_node` — hand-written minis (construction from
//     iterables with an observable adder, SameValueZero + -0 canonicalization,
//     forEach with live mutation, tombstone iteration, Map/Set iterator
//     sequencing, WeakMap/WeakSet weak-key validation, @@toStringTag/@@species,
//     user @@iterator for-of/spread/destructuring, IteratorClose on early
//     break/throw) run vs the real Node driver, each pinned Cover (byte-equal)
//     or Refuse (sound NoCoverage — never a wrong trace).
//   * `collection_corpus_sweep_vs_node` — an UNCAPPED sweep of every case under
//     test/built-ins/{Map,Set,WeakMap,WeakSet} + the Map/Set iterator dirs +
//     the language for-of user-iterable dirs, through BOTH heads. The bar: ZERO
//     wrong traces, ZERO panics; unmodeled surface is a sound NoCoverage.
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
    "test/built-ins/Map",
    "test/built-ins/Set",
    "test/built-ins/WeakMap",
    "test/built-ins/WeakSet",
    "test/built-ins/MapIteratorPrototype",
    "test/built-ins/SetIteratorPrototype",
    // The general iterator protocol over user-defined iterables.
    "test/language/statements/for-of",
    "test/language/expressions/spread",
];

fn driver_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs")
}

#[allow(clippy::too_many_arguments)]
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
    mf.write_all(manifest.to_string().as_bytes()).expect("write manifest");
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

#[allow(clippy::too_many_lines)]
fn cases() -> Vec<Case> {
    let mut v: Vec<Case> = Vec::new();
    let mut c = |name, expect, body| v.push(Case { name, expect, body });

    // ---- Map construction + basics --------------------------------------
    c("map-empty", C, "var m=new Map(); console.log(m.size, m.get('x'), m.has('x'));");
    c("map-from-iterable", C,
      "var m=new Map([['a',1],['b',2]]); console.log(m.size, m.get('a'), m.get('b'), m.get('c'));");
    c("map-set-chains", C,
      "var m=new Map(); console.log(m.set(1,2)===m, m.set(1,9).get(1), m.size);");
    c("map-delete", C,
      "var m=new Map([['a',1]]); console.log(m.delete('a'), m.delete('a'), m.size, m.has('a'));");
    c("map-clear", C,
      "var m=new Map([['a',1],['b',2]]); m.clear(); console.log(m.size, m.get('a'));");
    c("map-tag", C, "console.log(Object.prototype.toString.call(new Map()));");
    c("map-species", C, "console.log(Map[Symbol.species]===Map);");
    c("map-iterator-eq-entries", C,
      "console.log(Map.prototype[Symbol.iterator]===Map.prototype.entries);");
    c("map-ctor-no-new", C,
      "var t=false; try{ Map(); }catch(e){ t=e instanceof TypeError; } console.log(t);");
    c("map-nonobject-entry", C,
      "var t=false; try{ new Map([1,2]); }catch(e){ t=e instanceof TypeError; } console.log(t);");
    c("map-wrong-receiver", C,
      "var t=false; try{ Map.prototype.get.call(new Set()); }catch(e){ t=e instanceof TypeError; } console.log(t);");

    // ---- SameValueZero + -0 canonicalization ----------------------------
    c("map-nan-key", C,
      "var m=new Map(); m.set(NaN,1); console.log(m.get(NaN), m.has(NaN), m.size);");
    c("map-neg-zero", C,
      "var m=new Map(); m.set(-0,'z'); var k; for (var x of m.keys()) k=x; console.log(m.has(0), m.get(0), 1/k);");
    c("set-neg-zero-iter", C,
      "var s=new Set([-0]); var k; for (var x of s) k=x; console.log(s.has(0), 1/k);");
    c("map-object-key", C,
      "var k={}; var m=new Map(); m.set(k,7); console.log(m.get(k), m.get({}), m.has(k));");

    // ---- observable adder (AddEntriesFromIterable) ----------------------
    c("map-adder-observed", C,
      "var log=[]; class M extends Map { set(k,v){ log.push([k,v]); return super.set(k,v); } }\n\
       var m=new M([['a',1],['b',2]]); console.log(log, m.size);");
    c("set-adder-observed", C,
      "var log=[]; class S extends Set { add(v){ log.push(v); return super.add(v); } }\n\
       var s=new S([1,2,3]); console.log(log, s.size);");
    c("map-set-not-callable", C,
      "var t=false; try{ var m=new Map(); m.set=1; }catch(e){}\n\
       try{ Reflect.construct(Map,[[['a',1]]],function(){}); }catch(e){}\n\
       console.log('ok');");

    // ---- forEach --------------------------------------------------------
    c("map-foreach-order", C,
      "var m=new Map([['a',1],['b',2]]); var r=[]; m.forEach(function(v,k,mm){ r.push(k+'='+v+':'+(mm===m)); }); console.log(r);");
    c("set-foreach-args", C,
      "var s=new Set([5,6]); var r=[]; s.forEach(function(v,v2,ss){ r.push(v+'/'+v2+'/'+(ss===s)); }); console.log(r.join(','));");
    c("map-foreach-live-mutation", C,
      "var m=new Map([['a',1],['b',2]]); var r=[]; m.forEach(function(v,k){ r.push(k); if(k==='a') m.set('c',3); if(k==='b') m.delete('c'); }); console.log(r);");
    c("map-foreach-thisarg", C,
      "var m=new Map([['a',1]]); var r; m.forEach(function(){ r=this.tag; }, {tag:'T'}); console.log(r);");
    c("map-foreach-noncallable", C,
      "var t=false; try{ new Map().forEach(1); }catch(e){ t=e instanceof TypeError; } console.log(t);");

    // ---- iterators ------------------------------------------------------
    c("map-entries-seq", C,
      "var it=new Map([['a',1],['b',2]]).entries(); var a=it.next().value, b=it.next().value; console.log(a[0],a[1],b[0],b[1],it.next().done);");
    c("map-keys-values", C,
      "var m=new Map([['a',1],['b',2]]); var ks=[]; for (var k of m.keys()) ks.push(k); var vs=[]; for (var v of m.values()) vs.push(v); console.log(ks.join(','), vs.join(','));");
    c("map-forof-destructure", C,
      "var m=new Map([['a',1],['b',2]]); var r=[]; for (var [k,v] of m) r.push(k+v); console.log(r);");
    c("set-values-eq-keys", C,
      "console.log(Set.prototype.values===Set.prototype.keys, Set.prototype[Symbol.iterator]===Set.prototype.values);");
    c("set-forof", C,
      "var r=[]; for (var x of new Set([1,2,3])) r.push(x*10); console.log(r);");
    c("set-entries", C,
      "var r=[]; for (var e of new Set([5,6]).entries()) r.push(e[0]+'/'+e[1]); console.log(r);");
    c("map-iter-live-add", C,
      "var m=new Map([['a',1]]); var it=m.keys(); it.next(); m.set('b',2); console.log(it.next().value, it.next().done);");
    c("map-iter-live-delete", C,
      "var m=new Map([['a',1],['b',2],['c',3]]); var it=m.keys(); it.next(); m.delete('b'); console.log(it.next().value, it.next().done);");
    c("map-iter-after-clear", C,
      "var m=new Map([['a',1],['b',2]]); var it=m.keys(); m.clear(); console.log(it.next().done);");
    c("map-iter-tag", C,
      "console.log(new Map().entries()[Symbol.toStringTag], new Set().values()[Symbol.toStringTag]);");
    c("map-iter-next-wrong-recv", C,
      "var t=false; try{ new Map().keys().next.call(new Set().values()); }catch(e){ t=e instanceof TypeError; } console.log(t);");
    c("map-iter-projects-empty", C, "console.log(new Map([['a',1]]).keys());");
    c("map-forof-count", C,
      "var n=0; for (var p of new Map([['a',1],['b',2]])) n++; console.log(n);");

    // ---- WeakMap / WeakSet ----------------------------------------------
    c("weakmap-basic", C,
      "var k={}; var wm=new WeakMap(); wm.set(k,1); console.log(wm.get(k), wm.has(k), wm.delete(k), wm.has(k));");
    c("weakmap-primitive-key-throws", C,
      "var t=false; try{ new WeakMap().set(1,2); }catch(e){ t=e instanceof TypeError; } console.log(t);");
    c("weakmap-get-primitive-undef", C,
      "console.log(new WeakMap().get(1), new WeakMap().has('x'), new WeakMap().delete(2));");
    c("weakmap-symbol-key", C,
      "var s=Symbol('a'); var wm=new WeakMap(); wm.set(s,9); console.log(wm.get(s), wm.has(s));");
    c("weakmap-wellknown-symbol", C,
      "var wm=new WeakMap(); wm.set(Symbol.iterator,3); console.log(wm.get(Symbol.iterator));");
    c("weakmap-registered-symbol-throws", C,
      "var t=false; try{ new WeakMap().set(Symbol.for('x'),1); }catch(e){ t=e instanceof TypeError; } console.log(t);");
    c("weakset-basic", C,
      "var k={}; var ws=new WeakSet(); console.log(ws.add(k)===ws, ws.has(k), ws.delete(k), ws.has(k));");
    c("weakset-primitive-throws", C,
      "var t=false; try{ new WeakSet().add(5); }catch(e){ t=e instanceof TypeError; } console.log(t);");
    c("weakmap-tag", C,
      "console.log(Object.prototype.toString.call(new WeakMap()), Object.prototype.toString.call(new WeakSet()));");
    c("weakmap-no-species", C,
      "console.log(Object.getOwnPropertyDescriptor(WeakMap,Symbol.species));");
    c("weak-from-iterable", C,
      "var a={},b={}; var wm=new WeakMap([[a,1],[b,2]]); console.log(wm.get(a), wm.get(b));");

    // ---- Set-methods proposal: registered, calling refuses --------------
    c("set-union-registered", C,
      "console.log(typeof Set.prototype.union, Set.prototype.union.length);");
    c("set-union-call-refuses", R,
      "var s=new Set([1,2]).union(new Set([2,3])); console.log(s.size);");

    // ---- general iterator protocol over user iterables ------------------
    c("user-iterable-forof", C,
      "var obj={ [Symbol.iterator](){ var i=0; return { next(){ return i<3?{value:i++,done:false}:{value:undefined,done:true}; } }; } };\n\
       var r=[]; for (var x of obj) r.push(x); console.log(r);");
    c("user-iterable-destructure", C,
      "var obj={ [Symbol.iterator](){ var vs=[10,20,30]; var i=0; return { next(){ return i<vs.length?{value:vs[i++],done:false}:{done:true}; } }; } };\n\
       var [a,b]=obj; console.log(a,b);");
    c("user-iterable-new-map", C,
      "var obj={ [Symbol.iterator](){ var vs=[['a',1],['b',2]]; var i=0; return { next(){ return i<vs.length?{value:vs[i++],done:false}:{done:true}; } }; } };\n\
       var m=new Map(obj); console.log(m.get('a'), m.get('b'), m.size);");
    c("user-iterable-close-on-break", C,
      "var closed=false; var obj={ [Symbol.iterator](){ var i=0; return { next(){ return {value:i++,done:false}; }, return(){ closed=true; return {done:true}; } }; } };\n\
       for (var x of obj){ if(x===2) break; } console.log(closed);");
    c("user-iterable-close-on-throw", C,
      "var closed=false; var obj={ [Symbol.iterator](){ var i=0; return { next(){ return {value:i++,done:false}; }, return(){ closed=true; return {done:true}; } }; } };\n\
       var t=false; try{ for (var x of obj){ if(x===1) throw 'stop'; } }catch(e){ t=true; } console.log(closed, t);");
    c("user-iterable-next-throws", C,
      "var obj={ [Symbol.iterator](){ return { next(){ throw new TypeError('boom'); } }; } };\n\
       var t=false; try{ for (var x of obj){} }catch(e){ t=e instanceof TypeError; } console.log(t);");
    c("user-iterable-non-object-result", C,
      "var obj={ [Symbol.iterator](){ return { next(){ return 5; } }; } };\n\
       var t=false; try{ for (var x of obj){} }catch(e){ t=e instanceof TypeError; } console.log(t);");
    c("user-iterator-not-object", C,
      "var obj={ [Symbol.iterator](){ return 42; } };\n\
       var t=false; try{ for (var x of obj){} }catch(e){ t=e instanceof TypeError; } console.log(t);");
    c("no-iterator-throws", C,
      "var t=false; try{ for (var x of {}){} }catch(e){ t=e instanceof TypeError; } console.log(t);");
    c("map-forof-user-order", C,
      "var seen=[]; var obj={ [Symbol.iterator](){ var i=0; return { next(){ seen.push('n'+i); return {value:i,done:i++>=2}; } }; } };\n\
       for (var x of obj) seen.push('x'+x); console.log(seen);");

    // ---- IteratorClose precedence over an early completion (7.4.11) ------
    // A `return` from a for-of body IteratorCloses the iterator; a THROWING
    // `return()` PREEMPTS the return completion (step 5).
    c("forof-return-close-throws-preempts", C,
      "var err={}; var iter={ [Symbol.iterator](){ return this; }, next(){ return {done:false}; }, return(){ throw err; } };\n\
       function f(){ for (var k of iter){ return 0; } }\n\
       var caught; try{ f(); }catch(e){ caught=(e===err); } console.log(caught);");
    // A NON-OBJECT `return()` result on a return completion → TypeError (step 6).
    c("forof-return-close-nonobject-typeerror", C,
      "var iter={ [Symbol.iterator](){ return this; }, next(){ return {done:false}; }, return(){ return 5; } };\n\
       function f(){ for (var k of iter){ return 0; } }\n\
       var t=false; try{ f(); }catch(e){ t=e instanceof TypeError; } console.log(t);");
    // A THROW completion always wins over a throwing `return()` (step 4).
    c("forof-throw-close-original-wins", C,
      "var iter={ [Symbol.iterator](){ return this; }, next(){ return {done:false}; }, return(){ throw new RangeError(); } };\n\
       var t=false; try{ for (var k of iter){ throw new TypeError('orig'); } }catch(e){ t=e instanceof TypeError; } console.log(t);");
    // `break` closes the iterator; a normal `return()` result is required.
    c("forof-break-close-called", C,
      "var closed=0; var iter={ [Symbol.iterator](){ return this; }, next(){ return {value:1,done:false}; }, return(){ closed++; return {}; } };\n\
       for (var k of iter){ break; } console.log(closed);");
    // A derived-class `return 0` inside a for-of: the throwing `return()`
    // preempts the derived-class return-override TypeError.
    c("derived-class-return-override-for-of", C,
      "var error={n:'e'}; var iter={ [Symbol.iterator](){ return this; }, next(){ return {done:false}; }, return(){ throw error; } };\n\
       class C extends class {} { constructor(){ super(); for (var k of iter){ return 0; } } }\n\
       var caught; try{ new C(); }catch(e){ caught=(e===error); } console.log(caught);");

    // ---- Promise combinators IteratorClose on element-step abrupt --------
    // Invoke(constructor,"resolve") throws → IteratorClose the iterable.
    c("promise-all-resolve-error-close", C,
      "var cc=0; var it={}; it[Symbol.iterator]=function(){ return { next(){ return {value:null,done:false}; }, return(){ cc+=1; } }; };\n\
       Promise.resolve=function(){ throw new TypeError(); }; Promise.all(it); console.log(cc);");
    c("promise-race-resolve-error-close", C,
      "var cc=0; var it={}; it[Symbol.iterator]=function(){ return { next(){ return {value:null,done:false}; }, return(){ cc+=1; } }; };\n\
       Promise.resolve=function(){ throw new TypeError(); }; Promise.race(it); console.log(cc);");
    c("promise-allSettled-resolve-error-close", C,
      "var cc=0; var it={}; it[Symbol.iterator]=function(){ return { next(){ return {value:null,done:false}; }, return(){ cc+=1; } }; };\n\
       Promise.resolve=function(){ throw new TypeError(); }; Promise.allSettled(it); console.log(cc);");
    // Get(nextPromise,"then") throws → IteratorClose the iterable.
    c("promise-all-then-get-error-close", C,
      "var cc=0; var it={}; it[Symbol.iterator]=function(){ return { next(){ return {value:null,done:false}; }, return(){ cc+=1; } }; };\n\
       Promise.resolve=function(){ return Object.defineProperty({}, 'then', { get: function(){ throw new TypeError(); } }); };\n\
       Promise.all(it); console.log(cc);");
    // Invoke(nextPromise,"then") throws → IteratorClose the iterable.
    c("promise-all-then-call-error-close", C,
      "var cc=0; var it={}; it[Symbol.iterator]=function(){ return { next(){ return {value:null,done:false}; }, return(){ cc+=1; } }; };\n\
       Promise.resolve=function(){ return { then: function(){ throw new TypeError(); } }; };\n\
       Promise.all(it); console.log(cc);");

    v
}

#[test]
#[allow(clippy::too_many_lines)]
fn collection_adversarial_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP collection_adversarial_vs_node: set TRUST_JS_NODE to run");
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
        let out = run_node(&node, &driver, tmp.path(), &format!("coll-{ci}"), case.body, &[], false, true);
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
        "collection adversarial failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
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

/// Diagnostic (no Node): histogram of NoCoverage reasons over the sweep dirs.
#[test]
fn collection_refusal_reasons() {
    if std::env::var("TRUST_JS_COLL_REASONS").is_err() {
        eprintln!("SKIP collection_refusal_reasons: set TRUST_JS_COLL_REASONS (+ TRUST_JS262_CORPUS) to run");
        return;
    }
    let corpus = std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string());
    let corpus = PathBuf::from(corpus);
    let assert_src = std::fs::read_to_string(corpus.join("harness/assert.js")).unwrap_or_default();
    let sta_src = std::fs::read_to_string(corpus.join("harness/sta.js")).unwrap_or_default();
    let dirs: Vec<&str> = std::env::var("TRUST_JS_COLL_DIRS").ok()
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
                let key = reason.split(&['(', ':'][..]).next().unwrap_or(&reason).trim().to_string();
                *hist.entry(key).or_insert(0) += 1;
            }
        }
    }
    let mut rows: Vec<(&String, &u32)> = hist.iter().collect();
    rows.sort_by(|a, b| b.1.cmp(a.1));
    eprintln!("== collection refusal reason histogram ==");
    for (r, n) in rows {
        eprintln!("{n:5}  {r}");
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn collection_corpus_sweep_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP collection_corpus_sweep_vs_node: set TRUST_JS_NODE (and optionally \
                   TRUST_JS262_CORPUS / TRUST_JS_COLL_SWEEP_CAP / TRUST_JS_COLL_DIRS) to run");
        return;
    };
    let corpus = std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string());
    let corpus = PathBuf::from(corpus);
    assert!(corpus.join("harness/assert.js").is_file(), "corpus harness not found under {}", corpus.display());
    let cap = std::env::var("TRUST_JS_COLL_SWEEP_CAP").ok().and_then(|s| s.parse::<usize>().ok()).unwrap_or(usize::MAX);
    let driver = driver_path();
    assert!(driver.is_file(), "driver not found at {}", driver.display());

    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();
    let mut panics: Vec<String> = Vec::new();
    let mut covered = 0u64;
    let mut refused = 0u64;
    let mut equal = 0u64;
    let mut include_cache: std::collections::BTreeMap<String, String> = std::collections::BTreeMap::new();

    let override_dirs = std::env::var("TRUST_JS_COLL_DIRS").ok();
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
        "== collection corpus sweep: covered {covered} (equal {equal}) / refused {refused} / panics {} / wrong {} ==",
        panics.len(),
        failures.len()
    );
    assert!(panics.is_empty(), "TOTALITY VIOLATION — {} panic(s):\n{}", panics.len(), panics.join("\n"));
    assert!(
        failures.is_empty(),
        "collection corpus sweep failures (wrong trace is never acceptable) ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
