// Sem-side-only timing probe (NO Node): walk the RegExp/String/regexp-literal
// corpus dirs and time evaluate_case_opts on each, flushing the path BEFORE
// each eval so a hang identifies the culprit, and reporting any case slower
// than the threshold. Isolates Rust-side pathological performance from the
// Node-differential cost. Env-gated on TRUST_JS262_CORPUS presence.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::io::Write;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::time::Instant;
use trust_js_sem::evaluate_case_opts;

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

fn frontmatter(body: &str) -> (Vec<String>, Vec<String>) {
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
                    inner.trim_end_matches(']').split(',').map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty()),
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
                    inner.trim_end_matches(']').split(',').map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty()),
                );
            }
        }
    }
    (includes, flags)
}

fn collect(dir: &Path) -> Vec<PathBuf> {
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
    files
}

#[test]
fn regexp_perf_probe_sem_only() {
    if std::env::var("TRUST_JS_RE_PERF").is_err() {
        eprintln!("SKIP regexp_perf_probe_sem_only: set TRUST_JS_RE_PERF=1 to run");
        return;
    }
    let corpus = std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string());
    let corpus = PathBuf::from(corpus);
    let harness = |n: &str| std::fs::read_to_string(corpus.join("harness").join(n)).unwrap_or_default();
    let assert_js = harness("assert.js");
    let sta_js = harness("sta.js");
    let threshold_ms: u128 = std::env::var("TRUST_JS_RE_PERF_MS").ok().and_then(|s| s.parse().ok()).unwrap_or(300);

    let progress_path = std::env::var("TRUST_JS_RE_PERF_PROGRESS")
        .unwrap_or_else(|_| "/tmp/re_perf_progress.txt".to_string());

    let only = std::env::var("TRUST_JS_RE_PERF_ONLY").ok(); // substring filter
    let cap: usize = std::env::var("TRUST_JS_RE_PERF_CAP").ok().and_then(|s| s.parse().ok()).unwrap_or(usize::MAX);

    let mut slow: Vec<(u128, String)> = Vec::new();
    let mut panicked: Vec<String> = Vec::new();
    let mut n = 0u64;
    let mut taken = 0usize;
    'outer: for dir in SWEEP_DIRS {
        for path in collect(&corpus.join(dir)) {
            if let Some(sub) = &only {
                if !path.to_string_lossy().contains(sub.as_str()) {
                    continue;
                }
            }
            if taken >= cap {
                break 'outer;
            }
            taken += 1;
            let Ok(body) = std::fs::read_to_string(&path) else { continue };
            let (incs, flags) = frontmatter(&body);
            if flags.iter().any(|f| f == "async" || f == "module") {
                continue;
            }
            let raw = flags.iter().any(|f| f == "raw");
            let mut inc_src: Vec<String> = if raw { Vec::new() } else { vec![assert_js.clone(), sta_js.clone()] };
            let mut ok = true;
            for name in &incs {
                let p = corpus.join("harness").join(name);
                if !p.is_file() { ok = false; break; }
                inc_src.push(std::fs::read_to_string(&p).unwrap_or_default());
            }
            if !ok { continue; }
            let modes: &[bool] = if flags.iter().any(|f| f == "onlyStrict") { &[true] }
                else if raw || flags.iter().any(|f| f == "noStrict") { &[false] } else { &[false, true] };
            let rel = path.strip_prefix(&corpus).unwrap_or(&path).display().to_string();
            for &strict in modes {
                let body2 = if strict { format!("\"use strict\";\n{body}") } else { body.clone() };
                let refs: Vec<&str> = inc_src.iter().map(String::as_str).collect();
                // Write the path to a progress file BEFORE evaluating (explicit
                // flush): a hang leaves it as the last line.
                if let Ok(mut f) = std::fs::File::create(&progress_path) {
                    let _ = writeln!(f, "{n} {rel} [{}]", if strict { "s" } else { "b" });
                    let _ = f.flush();
                }
                n += 1;
                let t0 = Instant::now();
                let r = catch_unwind(AssertUnwindSafe(|| evaluate_case_opts(&refs, &body2, false)));
                let ms = t0.elapsed().as_millis();
                if r.is_err() {
                    panicked.push(format!("{rel} [{}]", if strict { "s" } else { "b" }));
                }
                if ms >= threshold_ms {
                    slow.push((ms, format!("{rel} [{}]", if strict { "s" } else { "b" })));
                }
            }
        }
    }
    eprintln!("\n== perf probe: {n} evals; {} slow (>= {threshold_ms}ms); {} panics ==", slow.len(), panicked.len());
    slow.sort_by(|a, b| b.0.cmp(&a.0));
    for (ms, name) in slow.iter().take(40) {
        eprintln!("  {ms}ms  {name}");
    }
    for p in &panicked {
        eprintln!("  PANIC  {p}");
    }
    assert!(panicked.is_empty(), "totality: {} panic(s)", panicked.len());
}
