// Env-gated corpus differential for the eval/Function-constructor and
// non-ASCII-identifier surfaces grown in the S1-eval campaign. Every covered
// case must be byte-for-byte trace-equal with the Node driver; refusals are
// sound and counted; a wrong trace or a panic is fatal. Mirrors the
// calibration assembly (assert.js + sta.js + frontmatter includes, modes from
// flags, completion witness off).
//
// Run: TRUST_JS_NODE=/path/to/node [TRUST_JS262_CORPUS=/path] \
//        RUSTC_BOOTSTRAP=1 cargo test -p trust-js-sem --test \
//        eval_identifiers_differential -- --nocapture
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

/// (directory, per-dir cap). Files are taken in sorted order (deterministic).
const SAMPLE_DIRS: &[(&str, usize)] = &[
    ("test/language/identifiers", 400),
    ("test/language/eval-code/direct", 400),
    ("test/language/eval-code/indirect", 200),
    ("test/built-ins/eval", 40),
    ("test/built-ins/Function", 600),
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
fn eval_identifiers_differential_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!(
            "SKIP eval_identifiers_differential_vs_node: set TRUST_JS_NODE (and optionally \
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
            let rel = path
                .strip_prefix(&corpus)
                .unwrap_or(&path)
                .display()
                .to_string();

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

    eprintln!("== eval/identifiers sample: covered {covered} (equal {equal}) / refused {refused} ==");
    for (dir, (c, r)) in &per_dir {
        eprintln!("  {dir}: covered {c} refused {r}");
    }
    let mut reasons: Vec<(u64, String, String)> = refusal_reasons
        .into_iter()
        .map(|(k, (n, sample))| (n, k, sample))
        .collect();
    reasons.sort_by(|a, b| b.0.cmp(&a.0));
    eprintln!("== top refusal reasons ==");
    for (n, reason, sample) in reasons.iter().take(40) {
        eprintln!("  {n} x {reason} (e.g. {sample})");
    }

    assert!(
        failures.is_empty(),
        "eval/identifiers sample failures (wrong trace is never acceptable) ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
