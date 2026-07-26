// Env-gated adversarial + corpus differential for the binary-data surface
// (ECMA-262 §25 ArrayBuffer/DataView, §23.2 %TypedArray% + the concrete Number
// typed arrays) grown onto the reference head: construction (length /
// buffer+offset+length / array-like / iterable / typed-array), the
// integer-indexed exotic (OOB→undefined/no-op, detached, canonical numeric
// keys), per-type element coercion (modular wrap, Uint8Clamped round-half-even,
// Float32/Float16 round-to-nearest-even), the accessors + @@toStringTag,
// DataView get/set byte order + bounds/detached TypeErrors, isView/@@species,
// and the projection (cls "ArrayBuffer"/"DataView"/"Object"). Every Cover case
// must be byte-for-byte trace-equal with the Node driver; Refuse cases pin the
// sound NoCoverage behavior (BigInt typed arrays, out-of-slice methods).
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
    let mut c = |name: &'static str, expect: Expect, body: &'static str| {
        v.push(Case { name, expect, body });
    };

    // ---- globals / typeof / harness population ---------------------------
    c("ta-typeof", C,
      "console.log(typeof Int8Array, typeof Float64Array, typeof Uint8ClampedArray, typeof Float16Array, typeof BigInt64Array, typeof ArrayBuffer, typeof DataView);");
    c("ta-typedarray-intrinsic", C,
      "console.log(Object.getPrototypeOf(Int8Array) === Object.getPrototypeOf(Float64Array), Object.getPrototypeOf(Int8Array).name);");
    c("ta-bpe", C,
      "console.log(Int8Array.BYTES_PER_ELEMENT, Float64Array.BYTES_PER_ELEMENT, Uint16Array.BYTES_PER_ELEMENT, Int8Array.prototype.BYTES_PER_ELEMENT);");
    c("ta-names", C,
      "console.log(Int8Array.name, Uint8ClampedArray.name, Float32Array.name, Int8Array.length);");

    // ---- ArrayBuffer ------------------------------------------------------
    c("ab-basic", C,
      "var b = new ArrayBuffer(8); console.log(b.byteLength, b.maxByteLength, b.resizable, b.detached, b);");
    c("ab-isview", C,
      "console.log(ArrayBuffer.isView(new Int8Array(1)), ArrayBuffer.isView(new DataView(new ArrayBuffer(1))), ArrayBuffer.isView({}), ArrayBuffer.isView([]));");
    c("ab-slice", C,
      "var b = new ArrayBuffer(8); var u = new Uint8Array(b); u[0]=1;u[1]=2;u[2]=3;u[3]=4;\n\
       var s = b.slice(1,3); var v = new Uint8Array(s); console.log(s.byteLength, v[0], v[1]);");
    c("ab-tostring-tag", C, "console.log(Object.prototype.toString.call(new ArrayBuffer(1)));");
    c("ab-species", C, "console.log(ArrayBuffer[Symbol.species] === ArrayBuffer);");
    c("ab-toindex-rangeerror", C,
      "var t=false; try { new ArrayBuffer(-1); } catch(e){ t = e instanceof RangeError; } console.log(t);");
    c("ab-resizable", C,
      "var b = new ArrayBuffer(4, {maxByteLength: 8}); console.log(b.byteLength, b.maxByteLength, b.resizable);\n\
       b.resize(6); console.log(b.byteLength);");
    c("ab-ctor-no-new", C,
      "var t=false; try { ArrayBuffer(8); } catch(e){ t = e instanceof TypeError; } console.log(t);");

    // ---- typed array construction ----------------------------------------
    c("ta-from-length", C, "var a = new Int8Array(3); console.log(a.length, a.byteLength, a.byteOffset, a[0], a);");
    c("ta-from-array", C, "console.log(new Int16Array([10,20,30]));");
    c("ta-from-arraylike", C, "console.log(new Uint8Array({length:2, 0:5, 1:6}));");
    // Iterable path via an iterator OBJECT source: the array iterator is
    // driven through the (now modeled) %IteratorPrototype% self-return + the
    // intrinsic step, so `new Int8Array([...].values())` is exact.
    c("ta-from-iterator-object", C, "console.log(new Int8Array([1,2,3].values()));");
    c("ta-from-typedarray", C, "var s = new Int32Array([1,2,3]); console.log(new Float64Array(s));");
    c("ta-from-buffer", C,
      "var b = new ArrayBuffer(8); var a = new Int8Array(b, 2, 3); console.log(a.length, a.byteOffset, a.byteLength, a.buffer === b);");
    c("ta-from-buffer-auto", C,
      "var b = new ArrayBuffer(8); var a = new Int16Array(b); console.log(a.length, a.byteOffset, a.byteLength);");
    c("ta-from-buffer-badoffset", C,
      "var b = new ArrayBuffer(8); var t=false; try { new Int32Array(b, 3); } catch(e){ t = e instanceof RangeError; } console.log(t);");
    c("ta-string-len", C, "console.log(new Int8Array('3').length, new Int8Array(true).length, new Int8Array(null).length);");
    c("ta-no-new", C,
      "var t=false; try { Int8Array(3); } catch(e){ t = e instanceof TypeError; } console.log(t);");
    c("ta-abstract-throws", C,
      "var TA = Object.getPrototypeOf(Int8Array); var t=false; try { new TA(); } catch(e){ t = e instanceof TypeError; } console.log(t);");

    // ---- element coercion -------------------------------------------------
    c("ta-int8-wrap", C, "console.log(new Int8Array([300, -1, 128, 127])[0], new Int8Array([300])[0], new Uint8Array([300, -1])[0], new Uint8Array([-1])[0]);");
    c("ta-clamp", C, "console.log(new Uint8ClampedArray([300,-5,1.5,2.5,3.5,0.5]).join(','));");
    c("ta-int-nan-inf", C, "console.log(new Int32Array([NaN, Infinity, -Infinity, 1.9, -1.9]).join(','));");
    c("ta-int16-32", C, "console.log(new Int16Array([70000])[0], new Uint32Array([-1])[0], new Uint16Array([-1])[0]);");
    c("ta-f32", C, "console.log(new Float32Array([0.1])[0], new Float32Array([1/3])[0]);");
    c("ta-f16", C, "console.log(new Float16Array([1.1])[0], new Float16Array([0.1])[0], new Float16Array([65520])[0], new Float16Array([1/3])[0]);");
    c("ta-f16-more", C, "console.log(new Float16Array([2.5, -2.5, 100000, 0.0001, NaN])[0], new Float16Array([100000])[0]);");
    c("ta-f64", C, "console.log(new Float64Array([0.1])[0], new Float64Array([1/3])[0]);");

    // ---- integer-indexed exotic ------------------------------------------
    c("ta-index-set", C, "var a = new Int8Array(3); a[0]=10; a[1]=20; a[2]=300; console.log(a[0],a[1],a[2],a);");
    c("ta-oob", C, "var a = new Int8Array(3); a[5]=9; a[-1]=9; console.log(a[5], a[-1], a[3], a.length, a);");
    c("ta-canonical-noncanonical", C, "var a = new Int8Array(3); a['1.5']=9; a['foo']=7; console.log(a['1.5'], a.foo, a[1], Object.keys(a).join(','));");
    c("ta-in-has", C, "var a = new Int8Array(3); console.log(0 in a, 2 in a, 3 in a, 'length' in a);");
    c("ta-delete", C, "var a = new Int8Array(3); console.log(delete a[0], delete a[5], a[0]);");
    c("ta-keys-names", C, "var a = new Int8Array([7,8]); console.log(Object.keys(a).join(','), Object.getOwnPropertyNames(a).join(','));");
    c("ta-getdesc", C, "var a = new Int8Array([5]); var d = Object.getOwnPropertyDescriptor(a, '0'); console.log(d.value, d.writable, d.enumerable, d.configurable);");
    c("ta-hasown", C, "var a = new Int8Array([5]); console.log(a.hasOwnProperty('0'), a.hasOwnProperty('1'), a.hasOwnProperty('length'));");

    // ---- accessors + tag --------------------------------------------------
    c("ta-accessors", C, "var b = new ArrayBuffer(16); var a = new Int32Array(b, 4, 2); console.log(a.buffer===b, a.byteLength, a.byteOffset, a.length);");
    c("ta-tostring-tag", C, "console.log(Object.prototype.toString.call(new Int8Array(1)), Object.prototype.toString.call(new Float64Array(1)));");
    c("ta-tostring-tag-getter", C, "console.log(Object.getOwnPropertyDescriptor(Object.getPrototypeOf(Int8Array).prototype, Symbol.toStringTag).get.call({}));");

    // ---- DataView ---------------------------------------------------------
    c("dv-basic", C, "var b = new ArrayBuffer(8); var d = new DataView(b, 2, 4); console.log(d.byteLength, d.byteOffset, d.buffer===b, d);");
    c("dv-byteorder", C,
      "var b = new ArrayBuffer(8); var d = new DataView(b); d.setInt16(0, 0x1234, true);\n\
       var u = new Uint8Array(b); console.log(u[0], u[1], d.getInt16(0,false).toString(16), d.getInt16(0,true).toString(16));");
    c("dv-int-types", C,
      "var d = new DataView(new ArrayBuffer(8));\n\
       d.setInt8(0,-1); d.setUint8(1,200); d.setInt32(2,-70000,true);\n\
       console.log(d.getInt8(0), d.getUint8(1), d.getInt32(2,true), d.getUint8(0));");
    c("dv-float", C,
      "var d = new DataView(new ArrayBuffer(8)); d.setFloat64(0, 1.5, true); console.log(d.getFloat64(0,true), d.getFloat64(0,false)===1.5);");
    c("dv-f32-f16", C,
      "var d = new DataView(new ArrayBuffer(8)); d.setFloat32(0, 0.1, true); d.setFloat16(4, 1.1, true); console.log(d.getFloat32(0,true), d.getFloat16(4,true));");
    c("dv-oob-range", C,
      "var d = new DataView(new ArrayBuffer(4)); var t=false; try { d.getInt32(2); } catch(e){ t = e instanceof RangeError; } console.log(t);");
    c("dv-tostring-tag", C, "console.log(Object.prototype.toString.call(new DataView(new ArrayBuffer(1))));");
    c("dv-not-buffer", C,
      "var t=false; try { new DataView({}); } catch(e){ t = e instanceof TypeError; } console.log(t);");

    // ---- methods ----------------------------------------------------------
    c("ta-fill", C, "console.log(new Int8Array([1,2,3,4]).fill(9,1,3));");
    c("ta-join", C, "console.log(new Int8Array([1,2,3]).join('-'), new Float64Array([]).join());");
    c("ta-indexof", C, "var a = new Int8Array([5,6,5]); console.log(a.indexOf(5), a.indexOf(5,1), a.lastIndexOf(5), a.indexOf(9), a.includes(6), a.includes(9));");
    c("ta-at", C, "var a = new Int8Array([10,20,30]); console.log(a.at(0), a.at(-1), a.at(5));");
    c("ta-reverse", C, "console.log(new Int8Array([1,2,3]).reverse());");
    c("ta-subarray", C, "var a = new Int8Array([1,2,3,4]); var s = a.subarray(1,3); s[0]=9; console.log(s.length, s[0], a[1]);");
    c("ta-slice", C, "var a = new Int8Array([1,2,3,4]); var s = a.slice(1,3); s[0]=9; console.log(s.length, s[0], a[1]);");
    c("ta-set-array", C, "var a = new Int8Array(4); a.set([10,20], 1); console.log(a.join(','));");
    c("ta-set-ta", C, "var a = new Int8Array(4); a.set(new Int8Array([10,20]), 2); console.log(a.join(','));");
    c("ta-set-range", C, "var a = new Int8Array(2); var t=false; try { a.set([1,2,3]); } catch(e){ t = e instanceof RangeError; } console.log(t);");
    c("ta-foreach", C, "var out=[]; new Int8Array([1,2,3]).forEach(function(v,i){ out.push(v*i); }); console.log(out.join(','));");
    c("ta-reduce", C, "console.log(new Int8Array([1,2,3,4]).reduce(function(a,b){ return a+b; }), new Int8Array([1,2,3]).reduce(function(a,b){ return a+b; }, 10));");
    c("ta-every-some", C, "var a = new Int8Array([2,4,6]); console.log(a.every(function(x){return x%2===0;}), a.some(function(x){return x>5;}));");
    c("ta-for-of", C, "var out=[]; for (var x of new Int8Array([7,8,9])) out.push(x); console.log(out.join(','));");
    c("ta-iterator-values", C, "var it = new Int8Array([5,6]).values(); console.log(it.next().value, it.next().value, it.next().done);");

    // ---- BigInt refusals (globals exist; construction/ops refuse) ---------
    c("bigint-typeof", C, "console.log(typeof BigInt64Array, typeof BigUint64Array, BigInt64Array.name, BigInt64Array.BYTES_PER_ELEMENT);");
    // BigInt typed arrays are now modeled (construction, ToBigInt element
    // coercion, 64-bit wrap); a self-checking body keeps the witness free of a
    // projected bigint (which the driver's Number.prototype.toString throws on).
    c("bigint-construct", C, "var a = new BigInt64Array([1n, 2n]); a[0] = (2n ** 63n); if (a[0] !== -(2n ** 63n) || a[1] !== 2n) throw 0;");
    c("bigint-set-num-throws", C, "var a = new BigUint64Array(1); try { a[0] = 5; throw 1; } catch (e) { if (!(e instanceof TypeError)) throw 2; }");
    // DataView BigInt64/BigUint64 access is still out of slice (sound refusal).
    c("bigint-dv-refuses", R, "new DataView(new ArrayBuffer(8)).getBigInt64(0);");

    // ---- method refusals (out of slice) ----------------------------------
    c("ta-sort-refuses", R, "new Int8Array([3,1,2]).sort();");
    c("ta-map-refuses", R, "new Int8Array([1,2,3]).map(function(x){return x*2;});");
    c("ta-copywithin-refuses", R, "new Int8Array([1,2,3,4]).copyWithin(0,2);");

    v
}

#[test]
#[allow(clippy::too_many_lines)]
fn typed_array_adversarial_vs_node() {
    let Some(node) = node_bin() else {
        eprintln!("SKIP typed_array_adversarial_vs_node: set TRUST_JS_NODE to run");
        return;
    };
    let driver = driver_path();
    assert!(driver.is_file(), "driver not found at {}", driver.display());
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();

    for (ci, case) in cases().iter().enumerate() {
        let sem = evaluate_case(&[], case.body);
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
            false,
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
        "typed-array adversarial failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Corpus sweep over the binary-data directories.
// ---------------------------------------------------------------------------

const SWEEP_DIRS: &[(&str, usize)] = &[
    ("test/built-ins/ArrayBuffer", 200),
    ("test/built-ins/DataView", 250),
    ("test/built-ins/TypedArray", 250),
    ("test/built-ins/TypedArrayConstructors", 250),
    ("test/built-ins/Uint8Array", 40),
    ("test/built-ins/Int32Array", 40),
    ("test/built-ins/Float64Array", 40),
];

struct Frontmatter {
    includes: Vec<String>,
    flags: Vec<String>,
    features: Vec<String>,
}

fn parse_frontmatter(body: &str) -> Frontmatter {
    let fm = body
        .split_once("/*---")
        .and_then(|(_, rest)| rest.split_once("---*/"))
        .map_or("", |(fm, _)| fm);
    let mut includes = Vec::new();
    let mut flags = Vec::new();
    let mut features = Vec::new();
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
        } else if let Some(rest) = t.strip_prefix("features:") {
            if let Some(inner) = rest.trim().strip_prefix('[') {
                features.extend(
                    inner
                        .trim_end_matches(']')
                        .split(',')
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty()),
                );
            }
        }
    }
    Frontmatter { includes, flags, features }
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
fn typed_array_corpus_vs_node() {
    let Some(node) = node_bin() else {
        eprintln!("SKIP typed_array_corpus_vs_node: set TRUST_JS_NODE (and optionally TRUST_JS262_CORPUS) to run");
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
            // Skip tests needing features outside the modeled slice (Atomics,
            // resizable-view-dependent, $262 detach helper).
            if fm.features.iter().any(|f| {
                f == "resizable-arraybuffer"
                    || f == "array-buffer-transfer"
                    || f == "Atomics"
                    || f == "SharedArrayBuffer"
            }) {
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

    eprintln!("== typed-array corpus: covered {covered} (equal {equal}) / refused {refused} ==");
    for (dir, (cc, rr)) in &per_dir {
        eprintln!("  {dir}: covered {cc} refused {rr}");
    }
    let mut rs: Vec<(u64, String, String)> =
        reasons.into_iter().map(|(k, (n, s))| (n, k, s)).collect();
    rs.sort_by(|a, b| b.0.cmp(&a.0));
    eprintln!("== top refusal reasons ==");
    for (n, reason, sample) in rs.iter().take(30) {
        eprintln!("  {n} x {reason} (e.g. {sample})");
    }
    assert!(
        failures.is_empty(),
        "typed-array corpus failures (wrong trace is never acceptable) ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
