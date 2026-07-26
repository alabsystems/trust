// Env-gated regression sweep for the class-heritage / async interaction the
// m2b gate surfaced: an async arrow in ClassHeritage position is an early
// SyntaxError, and an async FUNCTION superclass (callable, not a constructor)
// is a TypeError at ClassDefinitionEvaluation. Sweeps the class early-error
// and subclass directories (plus the whole class trees at a cap) and requires
// byte-for-byte trace-equality with the Node driver — a WRONG trace or a PANIC
// is fatal, refusals are sound. Skips loudly when TRUST_JS_NODE is unset.
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

const SWEEP_DIRS: &[(&str, usize)] = &[
    ("test/language/statements/class/elements/syntax/early-errors", 4000),
    ("test/language/expressions/class/elements/syntax/early-errors", 4000),
    ("test/language/statements/class/subclass", 600),
    ("test/language/expressions/class/subclass", 600),
    ("test/language/statements/class", 900),
    ("test/language/expressions/class", 900),
];

fn parse_fm(body: &str) -> (Vec<String>, Vec<String>) {
    let fm = body
        .split_once("/*---")
        .and_then(|(_, rest)| rest.split_once("---*/"))
        .map_or("", |(fm, _)| fm);
    let (mut includes, mut flags) = (Vec::new(), Vec::new());
    let mut lines = fm.lines().peekable();
    while let Some(line) = lines.next() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("includes:") {
            let rest = rest.trim();
            if let Some(inner) = rest.strip_prefix('[') {
                includes.extend(
                    inner.trim_end_matches(']').split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()),
                );
            } else {
                while let Some(next) = lines.peek() {
                    if let Some(item) = next.trim_start().strip_prefix("- ") {
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
                    inner.trim_end_matches(']').split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()),
                );
            }
        }
    }
    (includes, flags)
}

fn collect(dir: &Path, cap: usize) -> Vec<PathBuf> {
    let mut files = Vec::new();
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
fn class_heritage_async_sweep_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP class_heritage_async_sweep_vs_node: set TRUST_JS_NODE");
        return;
    };
    let corpus =
        PathBuf::from(std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string()));
    assert!(corpus.join("harness/assert.js").is_file(), "corpus not found");
    let driver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates")
        .join("trust-js-trace/js/trace_driver.mjs");

    let tmp = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();
    let (mut covered, mut refused, mut equal, mut panics) = (0u64, 0u64, 0u64, 0u64);
    let mut include_cache: BTreeMap<String, String> = BTreeMap::new();
    let mut seen: std::collections::HashSet<PathBuf> = std::collections::HashSet::new();
    let mut case_no = 0usize;

    for (dir, cap) in SWEEP_DIRS {
        for path in collect(&corpus.join(dir), *cap) {
            if !seen.insert(path.clone()) {
                continue;
            }
            let Ok(body) = std::fs::read_to_string(&path) else { continue };
            let (fm_inc, flags) = parse_fm(&body);
            if flags.iter().any(|f| f == "module" || f == "CanBlockIsRequired") {
                continue;
            }
            let raw = flags.iter().any(|f| f == "raw");
            let modes: &[bool] = if flags.iter().any(|f| f == "onlyStrict") {
                &[true]
            } else if raw || flags.iter().any(|f| f == "noStrict") {
                &[false]
            } else {
                &[false, true]
            };
            let mut inc_names: Vec<String> =
                if raw { Vec::new() } else { vec!["assert.js".into(), "sta.js".into()] };
            inc_names.extend(fm_inc);
            if flags.iter().any(|f| f == "async") && !inc_names.iter().any(|n| n == "doneprintHandle.js") {
                inc_names.push("doneprintHandle.js".into());
            }
            let mut inc_srcs = Vec::new();
            let mut inc_paths = Vec::new();
            let mut missing = false;
            for name in &inc_names {
                let p = corpus.join("harness").join(name);
                if !p.is_file() {
                    missing = true;
                    break;
                }
                let src = include_cache
                    .entry(name.clone())
                    .or_insert_with(|| std::fs::read_to_string(&p).expect("read include"));
                inc_srcs.push(src.clone());
                inc_paths.push(p.display().to_string());
            }
            if missing {
                continue;
            }
            let rel = path.strip_prefix(&corpus).unwrap_or(&path).display().to_string();

            for &strict in modes {
                case_no += 1;
                let sem_body = if strict { format!("\"use strict\";\n{body}") } else { body.clone() };
                let refs: Vec<&str> = inc_srcs.iter().map(String::as_str).collect();
                let sem = match catch_unwind(AssertUnwindSafe(|| evaluate_case_opts(&refs, &sem_body, false))) {
                    Ok(o) => o,
                    Err(_) => {
                        panics += 1;
                        failures.push(format!("{rel} [{}]: PANIC", strict));
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
                let bp = tmp.path().join(format!("c-{case_no}.js"));
                std::fs::write(&bp, &body).expect("write");
                let manifest = serde_json::json!({
                    "completion_witness": false, "includes": inc_paths,
                    "source": bp.display().to_string(), "mode": mode, "kind": "script",
                });
                let mp = tmp.path().join(format!("c-{case_no}.json"));
                std::fs::File::create(&mp).unwrap().write_all(manifest.to_string().as_bytes()).unwrap();
                let out = Command::new(&node).arg(&driver).arg(&mp)
                    .env("TZ", "UTC").env("LANG", "C").env("LC_ALL", "C").output().expect("node");
                let node_trace = match extract_trace(&out.stdout) {
                    Ok(t) => t,
                    Err(e) => {
                        failures.push(format!("{rel} [{mode}]: node extraction failed: {e}"));
                        continue;
                    }
                };
                if traces_equal(&sem_trace, &node_trace) {
                    equal += 1;
                } else {
                    failures.push(format!(
                        "{rel} [{mode}]: WRONG TRACE: {}",
                        explain_divergence(&sem_trace, &node_trace).unwrap_or_else(|| "?".into())
                    ));
                }
            }
        }
    }
    eprintln!("class heritage sweep: covered={covered} equal={equal} refused={refused} panics={panics}");
    assert!(
        failures.is_empty(),
        "class heritage sweep failures ({}):\n{}",
        failures.len(),
        failures.iter().take(50).cloned().collect::<Vec<_>>().join("\n")
    );
}
