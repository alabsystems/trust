// Env-gated corpus differential: sample the test262 directories covered by
// the grown S0 surfaces (descriptors, for-in/of, arguments, call/apply/bind,
// Math, template literals, Array/String prototype methods) and require that
// every covered case is byte-for-byte trace-equal with the Node driver —
// refusals are sound and counted, wrong traces are fatal. Mirrors the
// calibration assembly: includes = assert.js + sta.js + frontmatter includes,
// modes from flags, completion witness off.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::BTreeMap;
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

/// (directory, per-dir cap). Caps keep the runtime bounded; files are taken
/// in sorted order so the sample is deterministic.
const SAMPLE_DIRS: &[(&str, usize)] = &[
    ("test/built-ins/Object/defineProperty", 60),
    ("test/built-ins/Object/getOwnPropertyDescriptor", 40),
    ("test/built-ins/Object/getOwnPropertyNames", 30),
    ("test/built-ins/Object/keys", 30),
    ("test/built-ins/Object/freeze", 30),
    ("test/built-ins/Object/seal", 30),
    ("test/built-ins/Object/preventExtensions", 20),
    ("test/built-ins/Object/isFrozen", 20),
    ("test/built-ins/Object/isSealed", 20),
    ("test/built-ins/Object/isExtensible", 20),
    ("test/built-ins/Object/defineProperties", 20),
    ("test/built-ins/Function/prototype/call", 30),
    ("test/built-ins/Function/prototype/apply", 30),
    ("test/built-ins/Function/prototype/bind", 30),
    ("test/built-ins/Math/pow", 30),
    ("test/built-ins/Math/floor", 20),
    ("test/built-ins/Math/ceil", 20),
    ("test/built-ins/Math/abs", 20),
    ("test/built-ins/Math/max", 20),
    ("test/built-ins/Math/min", 20),
    ("test/built-ins/Math/round", 20),
    ("test/built-ins/Math/sign", 20),
    ("test/built-ins/Math/sqrt", 20),
    ("test/built-ins/Math/trunc", 20),
    ("test/built-ins/Array/prototype/indexOf", 30),
    ("test/built-ins/Array/prototype/lastIndexOf", 30),
    ("test/built-ins/Array/prototype/includes", 30),
    ("test/built-ins/Array/prototype/slice", 30),
    ("test/built-ins/Array/prototype/join", 30),
    ("test/built-ins/Array/prototype/push", 20),
    ("test/built-ins/Array/prototype/pop", 20),
    ("test/built-ins/Array/prototype/shift", 20),
    ("test/built-ins/Array/prototype/unshift", 20),
    ("test/built-ins/Array/prototype/forEach", 30),
    ("test/built-ins/Array/prototype/map", 30),
    ("test/built-ins/Array/prototype/filter", 30),
    ("test/built-ins/Array/prototype/reduce", 30),
    ("test/built-ins/Array/prototype/reduceRight", 30),
    ("test/built-ins/Array/prototype/every", 20),
    ("test/built-ins/Array/prototype/some", 20),
    ("test/built-ins/Array/prototype/find", 20),
    ("test/built-ins/Array/prototype/findIndex", 20),
    // Array Iterator objects (§23.1.5).
    ("test/built-ins/Array/prototype/values", 40),
    ("test/built-ins/Array/prototype/keys", 40),
    ("test/built-ins/Array/prototype/entries", 40),
    ("test/built-ins/Array/prototype/Symbol.iterator", 20),
    ("test/built-ins/ArrayIteratorPrototype", 40),
    ("test/built-ins/String/prototype/charAt", 30),
    ("test/built-ins/String/prototype/charCodeAt", 30),
    ("test/built-ins/String/prototype/indexOf", 30),
    ("test/built-ins/String/prototype/lastIndexOf", 20),
    ("test/built-ins/String/prototype/slice", 30),
    ("test/built-ins/String/prototype/substring", 30),
    ("test/built-ins/String/prototype/split", 40),
    ("test/built-ins/String/prototype/replace", 30),
    ("test/built-ins/String/prototype/trim", 30),
    ("test/built-ins/String/prototype/toLowerCase", 20),
    ("test/built-ins/String/prototype/toUpperCase", 20),
    ("test/language/statements/const/dstr", 60),
    ("test/language/statements/let/dstr", 60),
    ("test/language/statements/variable/dstr", 60),
    ("test/language/statements/function/dstr", 60),
    ("test/language/statements/for-of/dstr", 60),
    ("test/language/expressions/assignment/dstr", 80),
    ("test/language/expressions/arrow-function", 80),
    ("test/language/destructuring", 40),
    ("test/language/identifiers", 60),
    ("test/language/statements/class", 150),
    ("test/language/expressions/class", 150),
    // Private class elements (§15.7): the single biggest refusal bucket.
    ("test/language/statements/class/elements", 400),
    ("test/language/expressions/class/elements", 400),
    ("test/language/expressions/optional-chaining/member-modifiers-private-reference", 20),
    ("test/language/expressions/super", 60),
    ("test/language/expressions/new", 40),
    ("test/language/statements/for-in", 60),
    ("test/language/statements/for-of", 40),
    ("test/language/expressions/delete", 40),
    ("test/language/expressions/in", 30),
    ("test/language/arguments-object", 60),
    ("test/language/expressions/template-literal", 40),
    ("test/language/expressions/object", 60),
    // Generators (§27.3-27.5): the object graph + the resumable-machine slice.
    ("test/language/statements/generators", 120),
    ("test/language/expressions/generators", 120),
    ("test/built-ins/GeneratorFunction", 40),
    ("test/built-ins/GeneratorPrototype", 80),
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

fn collect_js_files(dir: &Path, cap: usize) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&d) else {
            continue;
        };
        let mut entries: Vec<PathBuf> = rd.filter_map(|e| e.ok().map(|e| e.path())).collect();
        entries.sort();
        for p in entries {
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|e| e == "js")
                && !p
                    .file_name()
                    .is_some_and(|n| n.to_string_lossy().ends_with("_FIXTURE.js"))
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
fn corpus_sample_differential_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!(
            "SKIP corpus_sample_differential_vs_node: set TRUST_JS_NODE (and optionally \
             TRUST_JS262_CORPUS) to run"
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

    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();
    let mut covered = 0u64;
    let mut refused = 0u64;
    let mut equal = 0u64;
    let mut per_dir: BTreeMap<&str, (u64, u64)> = BTreeMap::new(); // (covered, refused)
    let mut include_cache: BTreeMap<String, String> = BTreeMap::new();
    let mut refusal_reasons: BTreeMap<String, (u64, String)> = BTreeMap::new();

    let mut case_no = 0usize;
    for (dir, cap) in SAMPLE_DIRS {
        let files = collect_js_files(&corpus.join(dir), *cap);
        for path in files {
            let Ok(body) = std::fs::read_to_string(&path) else {
                continue;
            };
            let fm = parse_frontmatter(&body);
            if fm
                .flags
                .iter()
                .any(|f| f == "async" || f == "module" || f == "CanBlockIsRequired")
            {
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
                let sem_body = if strict {
                    format!("\"use strict\";\n{body}")
                } else {
                    body.clone()
                };
                let inc_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();
                let sem = evaluate_case_opts(&inc_refs, &sem_body, false);
                let sem_trace = match sem {
                    SemOutcome::Trace(t) => t,
                    SemOutcome::NoCoverage { reason } => {
                        refused += 1;
                        per_dir.entry(dir).or_default().1 += 1;
                        let e = refusal_reasons
                            .entry(reason)
                            .or_insert_with(|| (0, rel.clone()));
                        e.0 += 1;
                        continue;
                    }
                };
                covered += 1;
                per_dir.entry(dir).or_default().0 += 1;

                let mode = if strict { "strict" } else { "bare" };
                let body_path = tmp.path().join(format!("case-{case_no}.body.js"));
                std::fs::write(&body_path, &body).expect("write body");
                let manifest = serde_json::json!({
                    "completion_witness": false,
                    "includes": include_paths,
                    "source": body_path.display().to_string(),
                    "mode": mode,
                    "kind": "script",
                });
                let manifest_path = tmp.path().join(format!("case-{case_no}.manifest.json"));
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
                if traces_equal(&sem_trace, &node_trace) {
                    equal += 1;
                } else {
                    failures.push(format!(
                        "{rel} [{mode}]: WRONG TRACE: {}",
                        explain_divergence(&sem_trace, &node_trace)
                            .unwrap_or_else(|| "unlocalized".to_string())
                    ));
                }
            }
        }
    }

    eprintln!("== corpus sample: covered {covered} (equal {equal}) / refused {refused} ==");
    for (dir, (c, r)) in &per_dir {
        eprintln!("  {dir}: covered {c} refused {r}");
    }
    let mut reasons: Vec<(u64, String, String)> = refusal_reasons
        .into_iter()
        .map(|(k, (n, sample))| (n, k, sample))
        .collect();
    reasons.sort_by(|a, b| b.0.cmp(&a.0));
    eprintln!("== top refusal reasons ==");
    for (n, reason, sample) in reasons.iter().take(30) {
        eprintln!("  {n} x {reason} (e.g. {sample})");
    }

    assert!(
        failures.is_empty(),
        "corpus sample failures (wrong trace is never acceptable) ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
