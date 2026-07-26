// Env-gated FULL-S0 sem coverage estimator: re-derives the frozen S0 slice
// exactly per tests/js262/S0.toml's selection contract (verified against the
// pinned count + list sha256, failing closed on drift), then runs EVERY
// slice case through trust_js_sem::evaluate_case_opts (witness off) in its
// calibration modes and reports covered/refused with a reason histogram.
// When TRUST_JS_NODE is also set, every 25th covered run (a deterministic
// unbiased cross-section of the WHOLE covered set, not just the grown-
// surface directories) is verified byte-for-byte against the Node driver —
// any wrong trace fails the test. The recorded gate's frozen harness owns
// the official numbers; this quantifies growth before a gate run.
// Set TRUST_JS262_FULL=1 (and optionally TRUST_JS262_CORPUS) to run.
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
const S0_COUNT: usize = 35_346;
const S0_SHA256: &str = "8fe0ce3162fbd899bd7eb61531bd32ae2d7eab2f6ddc4a7909e03675cc0ac342";

const INCLUDE_PREFIXES: &[&str] = &["test/language/", "test/built-ins/"];
const EXCLUDE_PREFIXES: &[&str] = &[
    "test/intl402/",
    "test/staging/",
    "test/annexB/",
    "test/built-ins/Temporal/",
];
const EXCLUDE_SUFFIXES: &[&str] = &["_FIXTURE.js"];
const EXCLUDE_FLAGS: &[&str] = &["async", "module", "CanBlockIsTrue", "CanBlockIsFalse"];
const EXCLUDE_CONTENT: &[&str] = &["$262."];
const EXCLUDE_FEATURES: &[&str] = &[
    "Atomics",
    "SharedArrayBuffer",
    "Temporal",
    "tail-call-optimization",
    "IsHTMLDDA",
    "cross-realm",
    "host-gc-required",
];
const EXCLUDE_FEATURE_SUBSTRINGS: &[&str] = &["Intl"];

fn fm_block(body: &str) -> &str {
    body.split_once("/*---")
        .and_then(|(_, rest)| rest.split_once("---*/"))
        .map_or("", |(fm, _)| fm)
}

/// A YAML-lite list field: `key: [a, b]` or block-style `- a` lines.
fn fm_list(fm: &str, key: &str) -> Vec<String> {
    let prefix = format!("{key}:");
    let mut out = Vec::new();
    let mut lines = fm.lines().peekable();
    while let Some(line) = lines.next() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix(&prefix) {
            let rest = rest.trim();
            if let Some(inner) = rest.strip_prefix('[') {
                let inner = inner.trim_end_matches(']');
                out.extend(
                    inner
                        .split(',')
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty()),
                );
            } else {
                while let Some(next) = lines.peek() {
                    let nt = next.trim_start();
                    if let Some(item) = nt.strip_prefix("- ") {
                        out.push(item.trim().to_string());
                        lines.next();
                    } else {
                        break;
                    }
                }
            }
            break;
        }
    }
    out
}

fn proposal_features(corpus: &Path) -> Vec<String> {
    let txt = std::fs::read_to_string(corpus.join("features.txt")).expect("features.txt");
    let mut out = Vec::new();
    let mut in_section = false;
    for line in txt.lines() {
        let t = line.trim();
        if t.starts_with("##") {
            in_section = t.contains("Proposed language features");
            continue;
        }
        if in_section && !t.is_empty() && !t.starts_with('#') {
            out.push(t.to_string());
        }
    }
    out
}

#[test]
#[allow(clippy::too_many_lines)]
fn full_s0_sem_coverage_estimate() {
    if std::env::var("TRUST_JS262_FULL").is_err() {
        eprintln!("SKIP full_s0_sem_coverage_estimate: set TRUST_JS262_FULL=1 to run");
        return;
    }
    let corpus = std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.to_string());
    let corpus = PathBuf::from(corpus);
    let proposals = proposal_features(&corpus);

    // Enumerate candidate files under the include prefixes.
    let mut files: Vec<String> = Vec::new();
    let mut stack: Vec<PathBuf> = INCLUDE_PREFIXES.iter().map(|p| corpus.join(p)).collect();
    while let Some(d) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&d) else { continue };
        for e in rd.filter_map(Result::ok) {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "js") {
                let rel = p
                    .strip_prefix(&corpus)
                    .expect("under corpus")
                    .to_string_lossy()
                    .replace('\\', "/");
                files.push(rel);
            }
        }
    }
    files.sort();

    // Apply the selection contract.
    let mut slice: Vec<(String, String)> = Vec::new(); // (rel, body)
    let mut include_content_cache: BTreeMap<String, String> = BTreeMap::new();
    'file: for rel in files {
        if EXCLUDE_PREFIXES.iter().any(|p| rel.starts_with(p)) {
            continue;
        }
        if EXCLUDE_SUFFIXES.iter().any(|s| rel.ends_with(s)) {
            continue;
        }
        let body = std::fs::read_to_string(corpus.join(&rel)).expect("read case");
        if EXCLUDE_CONTENT.iter().any(|s| body.contains(s)) {
            continue;
        }
        let fm = fm_block(&body);
        let flags = fm_list(fm, "flags");
        if flags.iter().any(|f| EXCLUDE_FLAGS.contains(&f.as_str())) {
            continue;
        }
        let features = fm_list(fm, "features");
        for f in &features {
            if EXCLUDE_FEATURES.contains(&f.as_str())
                || EXCLUDE_FEATURE_SUBSTRINGS.iter().any(|s| f.contains(s))
                || proposals.contains(f)
            {
                continue 'file;
            }
        }
        for inc in fm_list(fm, "includes") {
            let content = include_content_cache
                .entry(inc.clone())
                .or_insert_with(|| {
                    std::fs::read_to_string(corpus.join("harness").join(&inc))
                        .unwrap_or_default()
                });
            if EXCLUDE_CONTENT.iter().any(|s| content.contains(s)) {
                continue 'file;
            }
        }
        slice.push((rel, body));
    }

    // Verify the derivation against the frozen pin — drift fails closed.
    assert_eq!(slice.len(), S0_COUNT, "S0 derivation drift (count)");
    let mut concat = String::new();
    for (rel, _) in &slice {
        concat.push_str(rel);
        concat.push('\n');
    }
    assert_eq!(
        trust_js_trace::sha256_hex(concat.as_bytes()),
        S0_SHA256,
        "S0 derivation drift (sha256)"
    );

    // Evaluate every case in its calibration modes.
    let assert_src = std::fs::read_to_string(corpus.join("harness/assert.js")).expect("assert");
    let sta_src = std::fs::read_to_string(corpus.join("harness/sta.js")).expect("sta");
    let node = std::env::var("TRUST_JS_NODE").ok();
    let driver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .join("trust-js-trace/js/trace_driver.mjs");
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut verified = 0u64;
    let mut failures: Vec<String> = Vec::new();
    let mut covered = 0u64;
    let mut refused = 0u64;
    let mut reasons: BTreeMap<String, u64> = BTreeMap::new();
    for (i, (rel, body)) in slice.iter().enumerate() {
        if i % 2000 == 0 {
            eprintln!("... {i}/{} ({rel})", slice.len());
        }
        let fm = fm_block(body);
        let flags = fm_list(fm, "flags");
        let raw = flags.iter().any(|f| f == "raw");
        let modes: &[bool] = if flags.iter().any(|f| f == "onlyStrict") {
            &[true]
        } else if raw || flags.iter().any(|f| f == "noStrict") {
            &[false]
        } else {
            &[false, true]
        };
        let mut includes: Vec<String> = Vec::new();
        if !raw {
            includes.push(assert_src.clone());
            includes.push(sta_src.clone());
            for inc in fm_list(fm, "includes") {
                includes.push(
                    include_content_cache
                        .get(&inc)
                        .cloned()
                        .unwrap_or_else(|| {
                            std::fs::read_to_string(corpus.join("harness").join(&inc))
                                .unwrap_or_default()
                        }),
                );
            }
        }
        let inc_refs: Vec<&str> = includes.iter().map(String::as_str).collect();
        for &strict in modes {
            let sem_body = if strict {
                format!("\"use strict\";\n{body}")
            } else {
                body.clone()
            };
            match evaluate_case_opts(&inc_refs, &sem_body, false) {
                SemOutcome::Trace(sem_trace) => {
                    covered += 1;
                    let Some(node) = &node else { continue };
                    if covered % 25 != 0 {
                        continue;
                    }
                    // Stride-sampled driver verification.
                    verified += 1;
                    let mut include_paths: Vec<String> = Vec::new();
                    if !raw {
                        include_paths
                            .push(corpus.join("harness/assert.js").display().to_string());
                        include_paths.push(corpus.join("harness/sta.js").display().to_string());
                        for inc in fm_list(fm, "includes") {
                            include_paths
                                .push(corpus.join("harness").join(inc).display().to_string());
                        }
                    }
                    let body_path = tmp.path().join("case.body.js");
                    std::fs::write(&body_path, body).expect("write body");
                    let manifest = serde_json::json!({
                        "completion_witness": false,
                        "includes": include_paths,
                        "source": body_path.display().to_string(),
                        "mode": if strict { "strict" } else { "bare" },
                        "kind": "script",
                    });
                    let manifest_path = tmp.path().join("case.manifest.json");
                    let mut mf = std::fs::File::create(&manifest_path).expect("manifest");
                    mf.write_all(manifest.to_string().as_bytes()).expect("write");
                    drop(mf);
                    let out = Command::new(node)
                        .arg(&driver)
                        .arg(&manifest_path)
                        .env("TZ", "UTC")
                        .env("LANG", "C")
                        .env("LC_ALL", "C")
                        .output()
                        .expect("spawn node driver");
                    match extract_trace(&out.stdout) {
                        Ok(node_trace) => {
                            if !traces_equal(&sem_trace, &node_trace) {
                                failures.push(format!(
                                    "{rel} [{}]: WRONG TRACE: {}",
                                    if strict { "strict" } else { "bare" },
                                    explain_divergence(&sem_trace, &node_trace)
                                        .unwrap_or_else(|| "unlocalized".to_string())
                                ));
                            }
                        }
                        Err(e) => failures.push(format!("{rel}: driver failed: {e}")),
                    }
                }
                SemOutcome::NoCoverage { reason } => {
                    refused += 1;
                    *reasons.entry(reason).or_default() += 1;
                }
            }
        }
    }

    let total = covered + refused;
    eprintln!("== FULL S0 sem coverage estimate ==");
    eprintln!("runs: {total}  covered: {covered}  refused: {refused}  stride-verified: {verified}");
    assert!(
        failures.is_empty(),
        "stride-verification failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
    let mut rs: Vec<(u64, String)> = reasons.into_iter().map(|(k, v)| (v, k)).collect();
    rs.sort_by(|a, b| b.0.cmp(&a.0));
    eprintln!("== top refusal reasons ==");
    for (n, reason) in rs.iter().take(40) {
        eprintln!("  {n} x {reason}");
    }
}
