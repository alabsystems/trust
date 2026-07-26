// TEMPORARY broad differential over the directories most affected by the
// s1d-divergence fixes (heritage private scoping, generator/arrow param
// [Yield], object/class `*`-prefix, generator-function IsConstructor,
// Object.prototype.toString on generators). Confirms zero NEW wrong traces
// across the real corpus. Env-gated on TRUST_JS_NODE. Not for commit.

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

const DIRS: &[(&str, usize)] = &[
    ("test/language/statements/class/elements/syntax", 4000),
    ("test/language/expressions/class/elements/syntax", 4000),
    ("test/language/statements/class/elements/private-methods", 400),
    ("test/language/expressions/class/elements/private-methods", 400),
    ("test/language/statements/class", 4000),
    ("test/language/expressions/class", 4000),
    ("test/language/expressions/object", 1500),
    ("test/language/statements/function", 800),
    ("test/language/expressions/function", 800),
    ("test/language/expressions/arrow-function", 600),
    ("test/language/statements/generators", 600),
    ("test/language/expressions/generators", 600),
];

struct Fm {
    includes: Vec<String>,
    flags: Vec<String>,
}

fn parse_fm(body: &str) -> Fm {
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
        }
    }
    Fm { includes, flags }
}

fn collect(dir: &Path, cap: usize) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&d) else { continue };
        let mut es: Vec<PathBuf> = rd.filter_map(|e| e.ok().map(|e| e.path())).collect();
        es.sort();
        for p in es {
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
fn broad_change_sweep_vs_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("SKIP broad_change_sweep_vs_node: set TRUST_JS_NODE");
        return;
    };
    let corpus =
        PathBuf::from(std::env::var("TRUST_JS262_CORPUS").unwrap_or_else(|_| DEFAULT_CORPUS.into()));
    if !corpus.join("harness/assert.js").is_file() {
        eprintln!("SKIP: corpus missing");
        return;
    }
    let driver = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("trust-js-trace/js/trace_driver.mjs");
    let tmp = tempfile::tempdir().unwrap();
    let mut inc_cache: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    let mut failures = Vec::new();
    let mut covered = 0u64;
    let mut refused = 0u64;
    let mut equal = 0u64;
    let mut case_no = 0usize;
    let mut seen: std::collections::HashSet<PathBuf> = std::collections::HashSet::new();

    for (dir, cap) in DIRS {
        for path in collect(&corpus.join(dir), *cap) {
            if !seen.insert(path.clone()) {
                continue;
            }
            let Ok(body) = std::fs::read_to_string(&path) else { continue };
            let fm = parse_fm(&body);
            if fm.flags.iter().any(|f| {
                f == "async" || f == "module" || f == "CanBlockIsRequired"
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
            let mut names: Vec<String> = if raw {
                Vec::new()
            } else {
                vec!["assert.js".into(), "sta.js".into()]
            };
            names.extend(fm.includes.iter().cloned());
            let mut srcs = Vec::new();
            let mut ipaths = Vec::new();
            let mut missing = false;
            for n in &names {
                let p = corpus.join("harness").join(n);
                if !p.is_file() {
                    missing = true;
                    break;
                }
                srcs.push(
                    inc_cache
                        .entry(n.clone())
                        .or_insert_with(|| std::fs::read_to_string(&p).unwrap())
                        .clone(),
                );
                ipaths.push(p.display().to_string());
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
                let refs: Vec<&str> = srcs.iter().map(String::as_str).collect();
                let sem = match evaluate_case_opts(&refs, &sem_body, false) {
                    SemOutcome::Trace(t) => t,
                    SemOutcome::NoCoverage { .. } => {
                        refused += 1;
                        continue;
                    }
                };
                covered += 1;
                let mode = if strict { "strict" } else { "bare" };
                let bp = tmp.path().join(format!("c{case_no}.js"));
                std::fs::write(&bp, &body).unwrap();
                let manifest = serde_json::json!({
                    "completion_witness": false, "includes": ipaths,
                    "source": bp.display().to_string(), "mode": mode, "kind": "script",
                });
                let mp = tmp.path().join(format!("c{case_no}.json"));
                std::fs::File::create(&mp)
                    .unwrap()
                    .write_all(manifest.to_string().as_bytes())
                    .unwrap();
                let out = Command::new(&node)
                    .arg(&driver)
                    .arg(&mp)
                    .env("TZ", "UTC")
                    .env("LANG", "C")
                    .env("LC_ALL", "C")
                    .output()
                    .unwrap();
                let nt = match extract_trace(&out.stdout) {
                    Ok(t) => t,
                    Err(e) => {
                        failures.push(format!("{rel} [{mode}]: node extract: {e}"));
                        continue;
                    }
                };
                if traces_equal(&sem, &nt) {
                    equal += 1;
                } else {
                    failures.push(format!(
                        "{rel} [{mode}]: WRONG: {}",
                        explain_divergence(&sem, &nt).unwrap_or_else(|| "?".into())
                    ));
                }
            }
        }
    }
    eprintln!("== broad sweep: covered {covered} (equal {equal}) refused {refused} ==");
    assert!(
        failures.is_empty(),
        "broad sweep wrong traces ({}):\n{}",
        failures.len(),
        failures.iter().take(80).cloned().collect::<Vec<_>>().join("\n")
    );
}
