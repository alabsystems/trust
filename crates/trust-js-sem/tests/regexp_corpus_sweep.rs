// Env-gated UNCAPPED corpus sweep for the RegExp surface: every case under
// test/built-ins/RegExp, test/built-ins/RegExpStringIteratorPrototype,
// test/built-ins/String/prototype/{match,matchAll,replace,replaceAll,search,
// split}, and test/language/literals/regexp runs through BOTH this reference
// head and the real Node driver. The bar: ZERO wrong traces (a covered case
// whose trace differs from Node) and ZERO panics (totality) — a case outside
// the modeled slice is a sound NoCoverage refusal, which is always acceptable.
// Skips loudly when TRUST_JS_NODE is unset. Set TRUST_JS_RE_SWEEP_CAP to bound
// files per directory (default: unbounded).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::io::Write;
use std::panic::{catch_unwind, AssertUnwindSafe};
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
    "test/built-ins/RegExp",
    "test/built-ins/RegExpStringIteratorPrototype",
    "test/built-ins/String/prototype/match",
    "test/built-ins/String/prototype/matchAll",
    "test/built-ins/String/prototype/replace",
    "test/built-ins/String/prototype/replaceAll",
    "test/built-ins/String/prototype/search",
    "test/built-ins/String/prototype/split",
    "test/language/literals/regexp",
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
fn regexp_corpus_sweep_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP regexp_corpus_sweep_vs_node: set TRUST_JS_NODE (and optionally \
                   TRUST_JS262_CORPUS / TRUST_JS_RE_SWEEP_CAP) to run");
        return;
    };
    let corpus = std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string());
    let corpus = PathBuf::from(corpus);
    assert!(
        corpus.join("harness/assert.js").is_file(),
        "corpus harness not found under {}",
        corpus.display()
    );
    let cap = std::env::var("TRUST_JS_RE_SWEEP_CAP")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(usize::MAX);
    let driver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs");
    assert!(driver.is_file(), "driver not found at {}", driver.display());

    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();
    let mut panics: Vec<String> = Vec::new();
    let mut covered = 0u64;
    let mut refused = 0u64;
    let mut equal = 0u64;
    let mut include_cache: std::collections::BTreeMap<String, String> =
        std::collections::BTreeMap::new();

    // The `property-escapes/generated/*` tests are a pure-MATCHER census over
    // huge code-point ranges: each takes seconds on the (frozen, independently
    // validated) trust-js-regexp VM, and the matcher's Unicode-property tables
    // are already differentiated against Node by trust-js-regexp's own
    // 956-triple suite. Skip that heavy subtree here (set TRUST_JS_RE_GENERATED=1
    // to include it) so the sweep exercises this crate's NEW object-model /
    // protocol logic in bounded time.
    let skip_generated = std::env::var("TRUST_JS_RE_GENERATED").is_err();

    // Optional focused override (comma-separated relative dirs).
    let override_dirs = std::env::var("TRUST_JS_RE_DIRS").ok();
    let dirs: Vec<&str> = match &override_dirs {
        Some(s) => s.split(',').map(str::trim).filter(|s| !s.is_empty()).collect(),
        None => SWEEP_DIRS.to_vec(),
    };

    let mut case_no = 0usize;
    for dir in dirs {
        let files = collect_js_files(&corpus.join(dir), cap);
        for path in files {
            if skip_generated && path.to_string_lossy().contains("property-escapes/generated") {
                continue;
            }
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
                // Totality: a panic is a bug — record it, never abort the sweep.
                let sem = match catch_unwind(AssertUnwindSafe(|| {
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

    eprintln!(
        "== regexp corpus sweep: covered {covered} (equal {equal}) / refused {refused} / \
         panics {} / wrong {} ==",
        panics.len(),
        failures.len()
    );
    assert!(
        panics.is_empty(),
        "TOTALITY VIOLATION — {} panic(s):\n{}",
        panics.len(),
        panics.join("\n")
    );
    assert!(
        failures.is_empty(),
        "regexp corpus sweep failures (wrong trace is never acceptable) ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
