// Env-gated corpus sweep for the async job model: the test262 Promise +
// async-function/async-arrow/await directories (which the general corpus
// sample deliberately skips via the `async` flag). Every covered case must be
// byte-for-byte trace-equal with the Node driver — refusals are sound and
// counted, a WRONG trace or a PANIC is fatal. Async-flagged tests assemble the
// `doneprintHandle.js` harness (declaring `$DONE`); a passing async test
// records `print('Test262:AsyncTestComplete')` during the microtask/timer
// drain, so the ordering our independent job model produces is checked against
// real V8's.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::BTreeMap;
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

/// (directory, per-dir cap). Caps are set high enough to cover each directory
/// in full (the async directories are small); files are taken in sorted order
/// for determinism.
const SWEEP_DIRS: &[(&str, usize)] = &[
    ("test/built-ins/Promise", 2000),
    ("test/built-ins/AsyncFunction", 200),
    ("test/language/statements/async-function", 400),
    ("test/language/expressions/async-function", 400),
    ("test/language/expressions/async-arrow-function", 400),
    ("test/language/expressions/await", 200),
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
                    inner.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()),
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
                    inner.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()),
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
fn async_corpus_sweep_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP async_corpus_sweep_vs_node: set TRUST_JS_NODE (and optionally TRUST_JS262_CORPUS)");
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
    let mut panics = 0u64;
    let mut per_dir: BTreeMap<&str, (u64, u64)> = BTreeMap::new(); // (covered, refused)
    let mut include_cache: BTreeMap<String, String> = BTreeMap::new();
    let mut refusal_reasons: BTreeMap<String, u64> = BTreeMap::new();

    let mut case_no = 0usize;
    for (dir, cap) in SWEEP_DIRS {
        for path in collect_js_files(&corpus.join(dir), *cap) {
            let Ok(body) = std::fs::read_to_string(&path) else { continue };
            let fm = parse_frontmatter(&body);
            if fm.flags.iter().any(|f| f == "module" || f == "CanBlockIsRequired") {
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
            // The test262 runner auto-includes the async harness (which defines
            // `$DONE`) for every `async`-flagged test, whether or not the
            // frontmatter lists it explicitly.
            if fm.flags.iter().any(|f| f == "async")
                && !include_names.iter().any(|n| n == "doneprintHandle.js")
            {
                include_names.push("doneprintHandle.js".to_string());
            }
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
                let sem_body =
                    if strict { format!("\"use strict\";\n{body}") } else { body.clone() };
                let inc_refs: Vec<&str> = include_srcs.iter().map(String::as_str).collect();
                // Totality: a panic is a hard failure, never allowed to abort
                // the sweep — capture it per-case.
                let sem = match catch_unwind(AssertUnwindSafe(|| {
                    evaluate_case_opts(&inc_refs, &sem_body, false)
                })) {
                    Ok(o) => o,
                    Err(_) => {
                        panics += 1;
                        failures.push(format!("{rel} [{}]: PANIC in sem", mode_str(strict)));
                        continue;
                    }
                };
                let sem_trace = match sem {
                    SemOutcome::Trace(t) => t,
                    SemOutcome::NoCoverage { reason } => {
                        refused += 1;
                        per_dir.entry(dir).or_default().1 += 1;
                        *refusal_reasons.entry(short_reason(&reason)).or_insert(0) += 1;
                        continue;
                    }
                };
                covered += 1;
                per_dir.entry(dir).or_default().0 += 1;

                let mode = mode_str(strict);
                let body_path = tmp.path().join(format!("c-{case_no}.body.js"));
                std::fs::write(&body_path, &body).expect("write body");
                let manifest = serde_json::json!({
                    "completion_witness": false,
                    "includes": include_paths,
                    "source": body_path.display().to_string(),
                    "mode": mode,
                    "kind": "script",
                });
                let manifest_path = tmp.path().join(format!("c-{case_no}.manifest.json"));
                let mut mf = std::fs::File::create(&manifest_path).expect("create manifest");
                mf.write_all(manifest.to_string().as_bytes()).expect("write manifest");
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
                        "{rel} [{mode}]: WRONG TRACE: {}",
                        explain_divergence(&sem_trace, &node_trace)
                            .unwrap_or_else(|| "unlocalized".to_string())
                    ));
                }
            }
        }
    }

    eprintln!("=== async corpus sweep ===");
    eprintln!("covered={covered} equal={equal} refused={refused} panics={panics}");
    for (dir, (cov, refu)) in &per_dir {
        eprintln!("  {dir}: covered={cov} refused={refu}");
    }
    eprintln!("--- top refusal reasons ---");
    let mut reasons: Vec<_> = refusal_reasons.iter().collect();
    reasons.sort_by(|a, b| b.1.cmp(a.1));
    for (reason, n) in reasons.iter().take(25) {
        eprintln!("  {n:>5}  {reason}");
    }
    assert!(
        failures.is_empty(),
        "async corpus sweep failures ({}):\n{}",
        failures.len(),
        failures.iter().take(60).cloned().collect::<Vec<_>>().join("\n")
    );
}

fn mode_str(strict: bool) -> &'static str {
    if strict {
        "strict"
    } else {
        "bare"
    }
}

/// Collapse a refusal reason to a stable bucket key (strip trailing specifics).
fn short_reason(r: &str) -> String {
    let r = r.split(" (out of slice)").next().unwrap_or(r);
    let r = r.split(':').next().unwrap_or(r);
    r.chars().take(80).collect()
}
