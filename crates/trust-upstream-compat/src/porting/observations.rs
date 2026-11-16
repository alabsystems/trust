//! Conservative reconciliation of pristine test identities with actual execution.
//!
//! An aggregate bootstrap exit is never a per-test result. Unsupported suite
//! expansion, adaptations without a typed mapping, and absent cases stay Unknown.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use serde::Serialize;

use super::{ProofUpstreamTest, sha256_bytes, split_words};
use crate::TestOutcome;

#[derive(Debug, Serialize, PartialEq, Eq)]
pub(super) struct InputClosure {
    files: BTreeMap<String, String>,
    errors: Vec<String>,
}

fn input_key(root: &Path, path: &Path) -> std::io::Result<String> {
    let invalid = || {
        std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "test input path is not a relative UTF-8 component sequence",
        )
    };
    path.strip_prefix(root)
        .map_err(|_| invalid())?
        .components()
        .map(|component| match component {
            std::path::Component::Normal(name) => name.to_str().ok_or_else(invalid),
            _ => Err(invalid()),
        })
        .collect::<Result<Vec<_>, _>>()
        .map(|components| components.join("/"))
}

pub(super) fn input_closure(root: &Path) -> InputClosure {
    fn visit(root: &Path, path: &Path, closure: &mut InputClosure) -> std::io::Result<()> {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();
            let kind = entry.file_type()?;
            if kind.is_dir() {
                visit(root, &path, closure)?;
            } else if kind.is_file() {
                closure.files.insert(input_key(root, &path)?, sha256_bytes(&fs::read(&path)?));
            } else {
                // Do not silently omit symlinked directories or external inputs.
                closure.errors.push(format!("unsupported input kind: {}", path.display()));
            }
        }
        Ok(())
    }
    let mut closure = InputClosure { files: BTreeMap::new(), errors: Vec::new() };
    if let Err(error) = visit(root, &root.join("tests"), &mut closure) {
        closure.errors.push(error.to_string());
    }
    closure
}

pub(super) fn closure_matches(before: &InputClosure, after: &InputClosure) -> bool {
    before.errors.is_empty() && after.errors.is_empty() && before == after
}

#[derive(Debug, Serialize)]
pub(super) struct InputAdmission {
    pristine: InputClosure,
    adapted: InputClosure,
    pub unresolved: Vec<String>,
}

pub(super) fn input_admission(
    local: &InputClosure,
    pristine: &Path,
    adapted: &Path,
) -> InputAdmission {
    let pristine = input_closure(pristine);
    let adapted = input_closure(adapted);
    let mut unresolved = Vec::new();
    if !local.errors.is_empty() || !pristine.errors.is_empty() || !adapted.errors.is_empty() {
        unresolved.push("test input closure could not be completely read".into());
    }
    for (path, original) in &pristine.files {
        let actual = local.files.get(path);
        if actual != Some(original) && actual != adapted.files.get(path) {
            unresolved.push(format!("unmapped input: {path}"));
        }
    }
    for path in local.files.keys() {
        // Account for every local-only fixture/support input in the compiletest
        // roots. Runner policy ledgers (tests/upstream-rust, tests/trust-added)
        // are control-plane inputs, not implicitly additional compiletest cases.
        if super::COMPILETEST_PREFIXES.iter().any(|prefix| path.starts_with(prefix))
            && !pristine.files.contains_key(path)
            && !adapted.files.contains_key(path)
        {
            unresolved.push(format!("local-only fixture/support input: {path}"));
        }
    }
    InputAdmission { pristine, adapted, unresolved }
}

#[derive(Debug, Serialize)]
pub(super) struct ExpectedCases {
    test_id: String,
    path: String,
    source_path: String,
    source_sha256: Option<String>,
    pristine_sha256: Option<String>,
    pristine_path: std::path::PathBuf,
    adapted_path: std::path::PathBuf,
    adapted_sha256: Option<String>,
    names: Vec<String>,
    unresolved: Vec<String>,
}

#[derive(Debug, Serialize)]
pub(super) struct Observation {
    pub name: String,
    pub path: String,
    pub outcome: TestOutcome,
    detail: String,
    line: usize,
    suite: usize,
    pub complete_suite: bool,
}

#[derive(Debug, Serialize)]
pub(super) struct Reconciled {
    pub test_id: String,
    pub outcome: TestOutcome,
    pub detail: String,
}

// A conservative supported subset, derived from bootstrap's test! declarations.
// Debuginfo/debuggers, coverage modes, and JS/GUI harnesses require their own
// independently expanded roster. They are deliberately not guessed here.
fn mode(path: &str) -> Option<&'static str> {
    match path.split('/').nth(1)? {
        "ui" | "ui-fulldeps" | "rustdoc-ui" => Some("ui"),
        "crashes" => Some("crashes"),
        "codegen-llvm" => Some("codegen"),
        "codegen-units" => Some("codegen-units"),
        "assembly-llvm" => Some("assembly"),
        "incremental" => Some("incremental"),
        "pretty" => Some("pretty"),
        "rustdoc-html" => Some("rustdoc-html"),
        "rustdoc-json" => Some("rustdoc-json"),
        "run-make" => Some("run-make"),
        _ => None,
    }
}

fn context_problem(extra: &str, host: Option<&str>, target: Option<&str>) -> Option<String> {
    let single =
        |value: Option<&str>| value.is_some_and(|v| !v.is_empty() && !v.contains([',', ' ', '\n']));
    if !single(host) || !single(target) || host != target {
        return Some("one explicit native host/target is required to bind test names".into());
    }
    // Do not interpret arbitrary bootstrap options as evidence-preserving. In
    // particular --compare-mode expands every suite, --bless rewrites inputs,
    // --run=never omits execution, and --nocapture can print counterfeit records.
    let args = split_words(extra);
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        if matches!(arg.as_str(), "--config" | "-j" | "--jobs") {
            i += 1;
            if i >= args.len() {
                return Some("bootstrap argument is missing its value".into());
            }
        } else if !(matches!(arg.as_str(), "-v" | "--verbose" | "--force-rerun" | "--run=always")
            || arg.starts_with("--config=")
            || arg.starts_with("--jobs=")
            || arg
                .strip_prefix("--test-args=--test-threads=")
                .is_some_and(|v| v.parse::<usize>().is_ok_and(|n| n > 0)))
        {
            return Some(format!("unresolved bootstrap argument can change case coverage: {arg}"));
        }
        i += 1;
    }
    None
}

pub(super) fn revisions(source: &str) -> Result<Vec<String>, String> {
    let mut revisions = Vec::new();
    let mut seen = BTreeSet::new();
    // Like FileDirectives, inspect the entire file, not just its leading comments.
    for line in source.lines() {
        let Some(mut directive) = line.trim().strip_prefix("//@").map(str::trim_start) else {
            continue;
        };
        let conditional = directive.starts_with('[');
        if conditional {
            let Some((_, rest)) = directive.split_once(']') else {
                return Err("malformed conditional directive".into());
            };
            directive = rest.trim_start();
        }
        let name = directive.split([':', ' ']).next().unwrap_or("");
        if name != "revisions" {
            continue;
        }
        if conditional {
            return Err("conditional revisions require independent compiletest discovery".into());
        }
        let Some(value) = directive.strip_prefix("revisions:") else {
            return Err("malformed revisions directive".into());
        };
        let values = value.split_whitespace().collect::<Vec<_>>();
        if values.is_empty() {
            return Err("empty revisions directive".into());
        }
        for revision in values {
            if !revision.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'-'))
                || matches!(revision, "true" | "false")
                || !seen.insert(revision.to_string())
            {
                return Err("invalid or duplicate revision".into());
            }
            revisions.push(revision.to_string());
        }
    }
    Ok(revisions)
}

pub(super) fn expected_cases(
    root: &Path,
    pristine: &Path,
    adapted: &Path,
    tests: &[ProofUpstreamTest],
    extra: &str,
    host: Option<&str>,
    target: Option<&str>,
) -> Vec<ExpectedCases> {
    let context = context_problem(extra, host, target);
    tests
        .iter()
        .map(|test| {
            let source_path = if test.path.starts_with("tests/run-make/") {
                format!("{}/rmake.rs", test.path)
            } else {
                test.path.clone()
            };
            let mut row = ExpectedCases {
                test_id: test.id.clone(),
                path: test.path.clone(),
                source_path: source_path.clone(),
                source_sha256: None,
                pristine_sha256: None,
                pristine_path: pristine.join(&source_path),
                adapted_path: adapted.join(&source_path),
                adapted_sha256: None,
                names: Vec::new(),
                unresolved: context.iter().cloned().collect(),
            };
            if test.path.split('/').any(|part| part == "auxiliary") {
                row.unresolved.push("auxiliary input is not an independently executed test".into());
            }
            let Some(mode) = mode(&test.path) else {
                row.unresolved.push("suite/mode expansion is not independently bound".into());
                return row;
            };
            let local = fs::read(root.join(&row.source_path)).ok();
            let original = fs::read(&row.pristine_path).ok();
            let adapted = fs::read(&row.adapted_path).ok();
            row.source_sha256 = local.as_deref().map(sha256_bytes);
            row.pristine_sha256 = original.as_deref().map(sha256_bytes);
            row.adapted_sha256 = adapted.as_deref().map(sha256_bytes);
            // The overlay is freshly recreated by this run's adapt_overlay and
            // active, reviewed patch manifest. It is the only supported mapping
            // for changed bytes at the SAME upstream path; no arbitrary local
            // weakening, rename, or replacement inherits the original identity.
            if local.is_some() && local != original && local != adapted {
                row.unresolved
                    .push("local input differs from pristine and canonical adapted bytes".into());
            }
            let parsed = |bytes: Option<&[u8]>| -> Result<Vec<String>, String> {
                let bytes = bytes.ok_or_else(|| {
                    "source absent; replacement/adaptation is unmeasured".to_string()
                })?;
                let source =
                    std::str::from_utf8(bytes).map_err(|_| "source is not UTF-8".to_string())?;
                revisions(source)
            };
            match (parsed(local.as_deref()), parsed(original.as_deref())) {
                (Ok(local), Ok(original)) if local == original => {
                    if mode == "run-make" && !local.is_empty() {
                        row.unresolved
                            .push("run-make revisions are unsupported by compiletest".into());
                    } else if local.is_empty() || mode == "incremental" {
                        // Incremental runs its entire revision sequence internally.
                        row.names.push(format!("[{mode}] {}", test.path));
                    } else {
                        row.names.extend(
                            local.iter().map(|rev| format!("[{mode}] {}#{rev}", test.path)),
                        );
                    }
                }
                (Ok(_), Ok(_)) => {
                    row.unresolved.push("pristine/local revision rosters differ".into())
                }
                (Err(error), _) | (_, Err(error)) => row.unresolved.push(error),
            }
            row
        })
        .collect()
}

fn terminal(line: &str) -> Option<(&str, TestOutcome, &str)> {
    let (name, status) = line.strip_prefix("test ")?.split_once(" ... ")?;
    let outcome = if status == "ok" || status.starts_with("ok (") && status.ends_with(')') {
        TestOutcome::Passed
    } else if status == "FAILED" || status.starts_with("FAILED (") && status.ends_with(')') {
        TestOutcome::Failed
    } else if status == "ignored"
        || status.starts_with("ignored, ")
        || status.starts_with("ignored (") && status.ends_with(')')
    {
        TestOutcome::Skipped
    } else {
        return None;
    };
    Some((name, outcome, status))
}

fn case_path(name: &str) -> Option<&str> {
    let (mode, path) = name.strip_prefix('[')?.split_once("] ")?;
    if mode.is_empty() || mode.contains(['[', ']']) || !path.starts_with("tests/") {
        return None;
    }
    let path = path.split_once('#').map_or(path, |(path, _)| path);
    (!path.split('/').any(|p| p.is_empty() || p == "." || p == "..")).then_some(path)
}

fn summary_counts(line: &str) -> Option<[usize; 3]> {
    let tail = line.strip_prefix("test result: ")?;
    let (verdict, tail) = tail.split_once(". ")?;
    let mut fields = tail.split(';').map(str::trim);
    let mut counts = [0; 3];
    for (count, suffix) in counts.iter_mut().zip([" passed", " failed", " ignored"]) {
        *count = fields.next()?.strip_suffix(suffix)?.parse().ok()?;
    }
    let measured: usize = fields.next()?.strip_suffix(" measured")?.parse().ok()?;
    let filtered: usize = fields.next()?.strip_suffix(" filtered out")?.parse().ok()?;
    if measured != 0 || filtered != 0 {
        return None;
    }
    if let Some(timing) = fields.next() {
        let seconds: f64 = timing.strip_prefix("finished in ")?.strip_suffix('s')?.parse().ok()?;
        if !seconds.is_finite() || seconds < 0.0 {
            return None;
        }
    }
    if fields.next().is_some() {
        return None;
    }
    match (verdict, counts[1]) {
        ("ok", 0) => Some(counts),
        ("FAILED", n) if n > 0 => Some(counts),
        _ => None,
    }
}

/// Parse only named terminal records inside a complete renderer suite. Never
/// consume captured failure stdout, summaries alone, progress notices, or a
/// replacement's similarly spelled name as evidence for another test.
pub(super) fn parse_log(log: &str) -> Vec<Observation> {
    let mut rows = Vec::<Observation>::new();
    let mut active = None::<(usize, usize, [usize; 3])>;
    let mut closed_start = None::<usize>;
    let mut suite = 0;
    let mut suite_identity = None::<String>;
    let mut mixed_suite = false;
    for (line_index, line) in log.lines().enumerate() {
        // Failure stdout is arbitrary text and can forge its own closing marker,
        // a summary, and subsequent suites. There is no authenticated framing in
        // this stream, so never resume positive evidence after entering details.
        if line == "failures:" || line == "benchmarks:" {
            break;
        }
        if line.starts_with("test result: ") {
            if let Some((start, expected, actual)) = active.take() {
                closed_start = Some(start);
                if let Some(counts) = summary_counts(line) {
                    let total = counts.iter().try_fold(0usize, |total, n| total.checked_add(*n));
                    let complete = !mixed_suite && counts == actual && total == Some(expected);
                    for row in &mut rows[start..] {
                        row.complete_suite = complete;
                    }
                }
            } else if let Some(start) = closed_start {
                // An unframed second summary makes the prior suite ambiguous.
                for row in &mut rows[start..] {
                    row.complete_suite = false;
                }
            }
            continue;
        }
        if let Some(count) = line
            .strip_prefix("running ")
            .and_then(|s| s.strip_suffix(" tests"))
            .and_then(|s| s.parse::<usize>().ok())
        {
            suite += 1;
            closed_start = None;
            active = Some((rows.len(), count, [0; 3]));
            suite_identity = None;
            mixed_suite = false;
            continue;
        }
        let Some((_, _, counts)) = &mut active else {
            continue;
        };
        let Some((name, outcome, detail)) = terminal(line) else {
            continue;
        };
        let index = match outcome {
            TestOutcome::Passed => 0,
            TestOutcome::Failed => 1,
            _ => 2,
        };
        if let Some(count) = counts[index].checked_add(1) {
            counts[index] = count;
        } else {
            mixed_suite = true;
        }
        if let Some(path) = case_path(name) {
            let identity = format!(
                "{}:{}",
                name.split_once("] ").unwrap().0,
                path.split('/').nth(1).unwrap_or("")
            );
            if suite_identity.as_ref().is_some_and(|previous| previous != &identity) {
                mixed_suite = true;
            }
            suite_identity = Some(identity);
            rows.push(Observation {
                name: name.into(),
                path: path.into(),
                outcome,
                detail: detail.into(),
                line: line_index + 1,
                suite,
                complete_suite: false,
            });
        } else {
            mixed_suite = true;
            if name.starts_with("[ui] ") {
                rows.push(Observation {
                    name: name.into(),
                    path: String::new(),
                    outcome,
                    detail: detail.into(),
                    line: line_index + 1,
                    suite,
                    complete_suite: false,
                });
            }
        }
    }
    rows
}

pub(super) fn reconcile(
    root: &Path,
    expected: &[ExpectedCases],
    observed: &[Observation],
) -> Vec<Reconciled> {
    let mut by_path = BTreeMap::<&str, Vec<&Observation>>::new();
    for row in observed {
        by_path.entry(&row.path).or_default().push(row);
    }
    expected
        .iter()
        .map(|test| {
            let rows = by_path.get(test.path.as_str()).map_or(&[][..], Vec::as_slice);
            let mut unresolved = test.unresolved.clone();
            let after = fs::read(root.join(&test.source_path)).ok().as_deref().map(sha256_bytes);
            if after != test.source_sha256 {
                unresolved.push("source changed during execution".into());
            }
            if fs::read(&test.pristine_path).ok().as_deref().map(sha256_bytes)
                != test.pristine_sha256
                || fs::read(&test.adapted_path).ok().as_deref().map(sha256_bytes)
                    != test.adapted_sha256
            {
                unresolved
                    .push("pristine or canonical adapted input changed during execution".into());
            }
            let expected_names = test.names.iter().map(String::as_str).collect::<BTreeSet<_>>();
            let mut names = BTreeMap::<&str, Vec<&Observation>>::new();
            for row in rows {
                names.entry(&row.name).or_default().push(row);
            }
            if names.keys().any(|name| !expected_names.contains(name)) {
                unresolved.push("unexpected revision, mode, or case identity".into());
            }
            if names.values().any(|rows| rows.len() != 1) {
                unresolved
                    .push("duplicate/conflicting case observations or multiple target runs".into());
            }
            if test.names.is_empty() || expected_names.iter().any(|name| !names.contains_key(name))
            {
                unresolved.push("one or more expected cases were not observed".into());
            }
            if rows.iter().any(|row| !row.complete_suite) {
                unresolved.push("incomplete or inconsistent renderer suite".into());
            }
            // Preserve actual negative observations even when other cases are absent.
            // The case artifact retains every missing, duplicate, and ignored detail.
            let outcome = if rows.iter().any(|row| row.outcome == TestOutcome::Failed) {
                TestOutcome::Failed
            } else if !unresolved.is_empty() {
                TestOutcome::Unknown
            } else if rows.iter().any(|row| row.outcome == TestOutcome::Skipped) {
                TestOutcome::Skipped
            } else {
                TestOutcome::Passed
            };
            let detail = format!(
                "{} expected case(s), {} terminal observation(s); {}",
                test.names.len(),
                rows.len(),
                if unresolved.is_empty() {
                    "all case identities reconciled; see case-evidence.json".into()
                } else {
                    unresolved.join("; ")
                }
            );
            Reconciled { test_id: test.test_id.clone(), outcome, detail }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    #[test]
    fn input_keys_preserve_components_and_reject_lossy_names() {
        let root = Path::new("root");
        assert_eq!(
            input_key(root, &root.join("tests").join("ui").join("a.rs")).unwrap(),
            "tests/ui/a.rs"
        );
        assert!(input_key(root, Path::new("elsewhere/tests/ui/a.rs")).is_err());
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStrExt;
            assert_eq!(
                input_key(root, &root.join("tests/ui/literal\\name.rs")).unwrap(),
                "tests/ui/literal\\name.rs"
            );
            assert!(
                input_key(root, &root.join(std::ffi::OsStr::from_bytes(b"tests/ui/\xff.rs")))
                    .is_err()
            );
        }
    }

    use super::*;

    struct Fixture(std::path::PathBuf);
    impl Fixture {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let path = std::env::temp_dir().join(format!(
                "trust-upstream-observations-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
        fn write(&self, path: &str, source: &str) {
            let path = self.0.join(path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, source).unwrap();
        }
        fn test(&self, path: &str, source: &str) -> ProofUpstreamTest {
            let file = if path.starts_with("tests/run-make/") {
                format!("{path}/rmake.rs")
            } else {
                path.into()
            };
            self.write(&file, source);
            self.write(&format!("pristine/{file}"), source);
            self.write(&format!("adapted/{file}"), source);
            ProofUpstreamTest {
                id: path.into(),
                path: path.into(),
                source_git_blob: Some("0".repeat(40)),
            }
        }
        fn roster(&self, tests: &[ProofUpstreamTest]) -> Vec<ExpectedCases> {
            expected_cases(
                &self.0,
                &self.0.join("pristine"),
                &self.0.join("adapted"),
                tests,
                "",
                Some("aarch64-apple-darwin"),
                Some("aarch64-apple-darwin"),
            )
        }
        fn outcomes(&self, tests: &[ProofUpstreamTest], log: &str) -> Vec<TestOutcome> {
            reconcile(&self.0, &self.roster(tests), &parse_log(log))
                .iter()
                .map(|r| r.outcome)
                .collect()
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }

    fn suite(rows: &[(&str, &str)]) -> String {
        let mut log = format!("running {} tests\n", rows.len());
        let mut counts = [0; 3];
        for (name, outcome) in rows {
            log.push_str(&format!("test {name} ... {outcome}\n"));
            counts[if *outcome == "ok" {
                0
            } else if *outcome == "FAILED" {
                1
            } else {
                2
            }] += 1;
        }
        let verdict = if counts[1] == 0 { "ok" } else { "FAILED" };
        log.push_str(&format!("test result: {verdict}. {} passed; {} failed; {} ignored; 0 measured; 0 filtered out\n", counts[0], counts[1], counts[2]));
        log
    }

    #[test]
    fn aggregate_zero_exit_cannot_manufacture_per_test_passes() {
        let f = Fixture::new();
        let tests = vec![
            f.test("tests/ui/seen.rs", "fn main() {}"),
            f.test("tests/ui/absent.rs", "fn main() {}"),
        ];
        let log = f.0.join("execution.log");
        fs::write(&log, suite(&[("[ui] tests/ui/seen.rs", "ok")])).unwrap();
        let proof = f.0.join("proof");
        fs::create_dir(&proof).unwrap();
        let sidecar = proof.join("compiletest-events-42-0.jsonl");
        let events = [
            serde_json::json!({"schema":"trust.compiletest.case-events/v1","type":"invocation","argv":["--suite","ui","--mode","ui","--host","aarch64-apple-darwin","--target","aarch64-apple-darwin"]}),
            serde_json::json!({"schema":"trust.compiletest.case-events/v1","type":"suite","event":"started","test_count":1,"selected_count":1}),
            serde_json::json!({"schema":"trust.compiletest.case-events/v1","type":"test","event":"started","name":"[ui] tests/ui/seen.rs"}),
            serde_json::json!({"schema":"trust.compiletest.case-events/v1","type":"test","event":"ok","name":"[ui] tests/ui/seen.rs","message":null,"stdout":null}),
            serde_json::json!({"schema":"trust.compiletest.case-events/v1","type":"suite","event":"ok","selected_count":1,"executed_count":1,"terminal_count":1,"protocol_valid":true,"protocol_error":null,"passed":1,"failed":0,"ignored":0,"measured":0,"filtered_out":0,"exec_time":0.1}),
        ];
        fs::write(&sidecar, events.iter().map(|event| format!("{event}\n")).collect::<String>())
            .unwrap();
        super::super::write_execution_proof_artifacts(
            &f.0,
            &proof,
            &"1".repeat(40),
            &"2".repeat(40),
            &tests,
            0,
            &super::super::empty_trust_added_execution(&proof),
            &log,
            "bootstrap test",
            false,
            &super::super::empty_test_exception_ledger(),
            "2026-09-17",
            &f.roster(&tests),
            &input_closure(&f.0),
            &input_admission(&input_closure(&f.0), &f.0.join("pristine"), &f.0.join("adapted")),
        )
        .unwrap();
        let results: serde_json::Value =
            serde_json::from_slice(&fs::read(proof.join("results.json")).unwrap()).unwrap();
        assert_eq!(results["results"][0]["outcome"], "passed");
        assert_eq!(results["results"][1]["outcome"], "unknown");
        let inventory: serde_json::Value =
            serde_json::from_slice(&fs::read(proof.join("inventory.json")).unwrap()).unwrap();
        assert_eq!(inventory["tests"].as_array().unwrap().len(), 2);
        assert_eq!(inventory["tests"][1]["path"], "tests/ui/absent.rs");
        assert!(proof.join("case-evidence.json").exists());
        let evidence: serde_json::Value =
            serde_json::from_slice(&fs::read(proof.join("case-evidence.json")).unwrap()).unwrap();
        assert_eq!(evidence["log_sha256"], sha256_bytes(&fs::read(&log).unwrap()));
        assert_eq!(evidence["aggregate_exit_status"], 0);
        assert_eq!(evidence["structured_sidecars"]["streams_valid"], true);
        assert_eq!(
            evidence["structured_sidecars"]["files"][0]["sha256"],
            sha256_bytes(&fs::read(&sidecar).unwrap())
        );
        assert!(
            evidence["structured_sidecars"]["authority"]
                .as_str()
                .unwrap()
                .contains("not independently authenticated")
        );
    }

    #[test]
    fn missing_ignored_failed_and_unrelated_records_remain_distinct() {
        let f = Fixture::new();
        let tests = ["yes", "skip", "fail", "missing"]
            .iter()
            .map(|name| f.test(&format!("tests/ui/{name}.rs"), "fn main() {}"))
            .collect::<Vec<_>>();
        let log = suite(&[
            ("[ui] tests/ui/yes.rs", "ok"),
            ("[ui] tests/ui/skip.rs", "ignored, up-to-date"),
            ("[ui] tests/ui/fail.rs", "FAILED"),
            ("[ui] tests/ui/unrelated.rs", "ok"),
        ]);
        assert_eq!(
            f.outcomes(&tests, &log),
            [TestOutcome::Passed, TestOutcome::Skipped, TestOutcome::Failed, TestOutcome::Unknown]
        );
    }

    #[test]
    fn every_revision_must_be_observed_and_no_ignored_revision_is_a_pass() {
        let f = Fixture::new();
        let tests = [f.test(
            "tests/ui/rev.rs",
            "//@ revisions: first\nfn main() {}\n//@ revisions: second\n",
        )];
        for (rows, expected) in [
            (vec![("[ui] tests/ui/rev.rs#first", "ok")], TestOutcome::Unknown),
            (
                vec![
                    ("[ui] tests/ui/rev.rs#first", "ok"),
                    ("[ui] tests/ui/rev.rs#second", "ignored"),
                ],
                TestOutcome::Skipped,
            ),
            (
                vec![("[ui] tests/ui/rev.rs#first", "ok"), ("[ui] tests/ui/rev.rs#second", "ok")],
                TestOutcome::Passed,
            ),
            (vec![("[ui] tests/ui/rev.rs", "ok")], TestOutcome::Unknown),
        ] {
            assert_eq!(f.outcomes(&tests, &suite(&rows)), [expected]);
        }
    }

    #[test]
    fn duplicate_conflicting_and_compare_mode_records_cannot_certify_coverage() {
        let f = Fixture::new();
        let tests = [f.test("tests/ui/a.rs", "fn main() {}")];
        assert_eq!(
            f.outcomes(
                &tests,
                &suite(&[("[ui] tests/ui/a.rs", "ok"), ("[ui] tests/ui/a.rs", "ok")])
            ),
            [TestOutcome::Unknown]
        );
        assert_eq!(
            f.outcomes(
                &tests,
                &suite(&[("[ui] tests/ui/a.rs", "ok"), ("[ui] tests/ui/a.rs", "FAILED")])
            ),
            [TestOutcome::Failed]
        );
        assert_eq!(
            f.outcomes(&tests, &suite(&[("[ui (next-solver)] tests/ui/a.rs", "ok")])),
            [TestOutcome::Unknown]
        );
        assert_eq!(
            f.outcomes(
                &tests,
                &(suite(&[("[ui] tests/ui/a.rs", "ok")]) + &suite(&[("[ui] tests/ui/a.rs", "ok")]))
            ),
            [TestOutcome::Unknown]
        );
    }

    #[test]
    fn deleted_tests_keep_original_identity_and_do_not_inherit_replacement_results() {
        let f = Fixture::new();
        let tests = [
            f.test("tests/crashes/135122.rs", "invalid Rust"),
            f.test("tests/ui/dist/cranelift.rs", "fn main() {}"),
        ];
        fs::remove_file(f.0.join("tests/crashes/135122.rs")).unwrap();
        fs::remove_file(f.0.join("tests/ui/dist/cranelift.rs")).unwrap();
        let log = suite(&[
            ("[ui] tests/ui/implied-bounds/ice-implied-outlives-bounds-135122.rs", "ok"),
            ("[ui] tests/ui/hello.rs", "ok"),
        ]);
        assert_eq!(f.outcomes(&tests, &log), [TestOutcome::Unknown, TestOutcome::Unknown]);
    }

    #[test]
    fn terse_summaries_and_progress_notices_are_not_terminal_observations() {
        let f = Fixture::new();
        let tests = [f.test("tests/run-make/example", "fn main() {}")];
        let log = "running 1 tests\ntest [run-make] tests/run-make/example has been running for a long time\n.\ntest result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n";
        assert_eq!(f.outcomes(&tests, log), [TestOutcome::Unknown]);
        assert_eq!(
            f.outcomes(&tests, &suite(&[("[run-make] tests/run-make/example/nested", "ok")])),
            [TestOutcome::Unknown]
        );
        assert_eq!(
            f.outcomes(&tests, &suite(&[("[run-make] tests/run-make/example", "ok")])),
            [TestOutcome::Passed]
        );
    }

    #[test]
    fn failed_stdout_cannot_supply_fake_running_test_or_summary_lines() {
        let f = Fixture::new();
        let tests =
            [f.test("tests/ui/a.rs", "fn main() {}"), f.test("tests/ui/b.rs", "fn main() {}")];
        let log = format!(
            "running 1 tests\ntest [ui] tests/ui/a.rs ... FAILED\nfailures:\n---- [ui] tests/ui/a.rs stdout ----\n{}---- [ui] tests/ui/a.rs stdout end ----\nfailures:\n    [ui] tests/ui/a.rs\ntest result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out\n",
            suite(&[("[ui] tests/ui/b.rs", "ok")])
        );
        assert_eq!(f.outcomes(&tests, &log), [TestOutcome::Failed, TestOutcome::Unknown]);
        let forged = format!(
            "running 1 tests\ntest [ui] tests/ui/a.rs ... FAILED\nfailures:\n---- [ui] tests/ui/a.rs stdout ----\n---- [ui] tests/ui/a.rs stdout end ----\ntest result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out\n{}",
            suite(&[("[ui] tests/ui/b.rs", "ok")])
        );
        assert_eq!(f.outcomes(&tests, &forged), [TestOutcome::Failed, TestOutcome::Unknown]);
    }

    #[test]
    fn changed_source_and_removed_revision_are_unmeasured() {
        let f = Fixture::new();
        let tests = [f.test("tests/ui/a.rs", "//@ revisions: first second\nfn main() {}")];
        f.write("tests/ui/a.rs", "//@ revisions: first\nfn main() {}");
        assert_eq!(
            f.outcomes(&tests, &suite(&[("[ui] tests/ui/a.rs#first", "ok")])),
            [TestOutcome::Unknown]
        );
        let tests = [f.test("tests/ui/b.rs", "fn main() {}")];
        let roster = f.roster(&tests);
        f.write("tests/ui/b.rs", "fn main() { panic!() }");
        assert_eq!(
            reconcile(&f.0, &roster, &parse_log(&suite(&[("[ui] tests/ui/b.rs", "ok")])))[0]
                .outcome,
            TestOutcome::Unknown
        );
    }

    #[test]
    fn unsupported_context_auxiliary_and_incremental_population_are_explicit() {
        let f = Fixture::new();
        let tests = [f.test("tests/incremental/a.rs", "//@ revisions: one two\nfn main() {}")];
        assert_eq!(
            f.outcomes(&tests, &suite(&[("[incremental] tests/incremental/a.rs", "ok")])),
            [TestOutcome::Passed]
        );
        for arg in [
            "--compare-mode next-solver",
            "--bless",
            "--no-capture",
            "--test-args=--nocapture",
            "--run=never",
            "--set rust.verbose-tests=false",
        ] {
            assert!(context_problem(arg, Some("host"), Some("host")).is_some(), "{arg}");
        }
        assert!(context_problem("", None, None).is_some());
        assert!(context_problem("", Some("one"), Some("two")).is_some());
        let tests = [
            f.test("tests/ui/auxiliary/a.rs", "fn main() {}"),
            f.test("tests/debuginfo/a.rs", "fn main() {}"),
        ];
        assert_eq!(
            f.outcomes(
                &tests,
                &suite(&[
                    ("[ui] tests/ui/auxiliary/a.rs", "ok"),
                    ("[debuginfo] tests/debuginfo/a.rs", "ok")
                ])
            ),
            [TestOutcome::Unknown, TestOutcome::Unknown]
        );
    }

    #[test]
    fn top_level_auxiliary_is_bound_as_input_but_never_as_a_passing_case() {
        let f = Fixture::new();
        let tests = [
            f.test("tests/auxiliary/minicore.rs", "pub fn support() {}"),
            f.test("tests/ui/a.rs", "fn main() {}"),
        ];
        let before = input_closure(&f.0);
        assert!(before.files.contains_key("tests/auxiliary/minicore.rs"));
        assert!(
            input_admission(&before, &f.0.join("pristine"), &f.0.join("adapted"))
                .unresolved
                .is_empty()
        );
        let roster = f.roster(&tests);
        assert!(roster[0].names.is_empty());
        assert!(roster[0].unresolved.iter().any(|reason| reason.contains("auxiliary input")));
        let log = suite(&[("[auxiliary] tests/auxiliary/minicore.rs", "ok")])
            + &suite(&[("[ui] tests/ui/a.rs", "ok")]);
        assert_eq!(
            reconcile(&f.0, &roster, &parse_log(&log))
                .iter()
                .map(|row| row.outcome)
                .collect::<Vec<_>>(),
            [TestOutcome::Unknown, TestOutcome::Passed]
        );
        f.write("tests/auxiliary/minicore.rs", "pub fn weakened() {}");
        assert!(!closure_matches(&before, &input_closure(&f.0)));
        assert!(
            input_admission(&input_closure(&f.0), &f.0.join("pristine"), &f.0.join("adapted"))
                .unresolved
                .iter()
                .any(|reason| reason.contains("tests/auxiliary/minicore.rs"))
        );
    }

    #[test]
    fn incomplete_or_count_inconsistent_suite_is_not_a_pass() {
        let f = Fixture::new();
        let tests = [f.test("tests/ui/a.rs", "fn main() {}")];
        for log in [
            "running 1 tests\ntest [ui] tests/ui/a.rs ... ok\n",
            "running 2 tests\ntest [ui] tests/ui/a.rs ... ok\ntest result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n",
        ] {
            assert_eq!(f.outcomes(&tests, log), [TestOutcome::Unknown]);
        }
        for summary in [
            "test result: FAILED. 1 passed; 0 failed; 0 ignored",
            "test result: alien. 1 passed; 0 failed; 0 ignored",
            "test result: ok. 1 passed; 1 failed; 0 ignored",
        ] {
            assert!(summary_counts(summary).is_none());
            assert_eq!(
                f.outcomes(
                    &tests,
                    &format!("running 1 tests\ntest [ui] tests/ui/a.rs ... ok\n{summary}\n")
                ),
                [TestOutcome::Unknown]
            );
        }
        let huge = format!(
            "running {} tests\ntest [ui] tests/ui/a.rs ... ok\ntest result: ok. {} passed; 0 failed; 1 ignored\n",
            usize::MAX,
            usize::MAX
        );
        assert_eq!(f.outcomes(&tests, &huge), [TestOutcome::Unknown]);
    }

    #[test]
    fn filtered_or_measured_summary_cannot_admit_visible_case() {
        let f = Fixture::new();
        let tests = [f.test("tests/ui/a.rs", "fn main() {}")];
        for tail in [
            "0 measured; 1 filtered out",
            "1 measured; 0 filtered out",
            "0 measured; 0 filtered out; 1 filtered out",
        ] {
            let log = format!(
                "running 1 tests\ntest [ui] tests/ui/a.rs ... ok\ntest result: ok. 1 passed; 0 failed; 0 ignored; {tail}\n"
            );
            assert_eq!(f.outcomes(&tests, &log), [TestOutcome::Unknown], "{tail}");
        }
        let repeated = "running 1 tests\ntest [ui] tests/ui/a.rs ... ok\ntest result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1 filtered out\ntest result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n";
        assert_eq!(f.outcomes(&tests, repeated), [TestOutcome::Unknown]);
        let complete = "running 1 tests\ntest [ui] tests/ui/a.rs ... ok\ntest result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n";
        assert_eq!(f.outcomes(&tests, complete), [TestOutcome::Passed]);
    }

    #[test]
    fn abbreviated_summary_cannot_complete_or_reconcile_suite() {
        let f = Fixture::new();
        let tests = [f.test("tests/ui/a.rs", "fn main() {}")];
        let complete = suite(&[("[ui] tests/ui/a.rs", "ok")]);
        assert_eq!(summary_counts(complete.lines().last().unwrap()), Some([1, 0, 0]));
        assert_eq!(f.outcomes(&tests, &complete), [TestOutcome::Passed]);

        for summary in [
            "test result: ok. 1 passed; 0 failed; 0 ignored",
            "test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured",
        ] {
            assert_eq!(summary_counts(summary), None, "{summary}");
            let log = format!("running 1 tests\ntest [ui] tests/ui/a.rs ... ok\n{summary}\n");
            let observed = parse_log(&log);
            assert_eq!(observed.len(), 1, "{summary}");
            assert!(!observed[0].complete_suite, "{summary}");
            assert_eq!(
                reconcile(&f.0, &f.roster(&tests), &observed)[0].outcome,
                TestOutcome::Unknown,
                "{summary}"
            );
        }
    }

    #[test]
    fn extra_summary_cannot_leave_prior_suite_complete() {
        let f = Fixture::new();
        let tests =
            [f.test("tests/ui/a.rs", "fn main() {}"), f.test("tests/ui/b.rs", "fn main() {}")];
        let first = suite(&[("[ui] tests/ui/a.rs", "ok")]);
        let second = suite(&[("[ui] tests/ui/b.rs", "ok")]);
        assert_eq!(f.outcomes(&tests, &(first.clone() + &second)), [TestOutcome::Passed; 2]);
        let repeated = format!("{first}{}\n{second}", first.lines().last().unwrap());
        assert_eq!(f.outcomes(&tests, &repeated), [TestOutcome::Unknown, TestOutcome::Passed]);
        let contradictory =
            "test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out\n";
        assert_eq!(
            f.outcomes(&tests, &(first + contradictory + &second)),
            [TestOutcome::Unknown, TestOutcome::Passed]
        );
    }

    #[test]
    fn auxiliary_expected_output_and_run_make_resource_changes_invalidate_input_closure() {
        let f = Fixture::new();
        f.test("tests/ui/a.rs", "fn main() {}");
        for path in
            ["tests/ui/auxiliary/a.rs", "tests/ui/a.stderr", "tests/run-make/example/data.bin"]
        {
            f.write(path, "before");
            let before = input_closure(&f.0);
            assert!(closure_matches(&before, &input_closure(&f.0)));
            f.write(path, "after");
            assert!(!closure_matches(&before, &input_closure(&f.0)), "{path}");
        }
    }

    #[test]
    fn preexisting_body_weakening_requires_exact_canonical_adaptation() {
        let f = Fixture::new();
        let tests = [f.test("tests/ui/a.rs", "fn main() { panic!() }")];
        f.write("tests/ui/a.rs", "fn main() {}");
        let log = suite(&[("[ui] tests/ui/a.rs", "ok")]);
        assert_eq!(f.outcomes(&tests, &log), [TestOutcome::Unknown]);
        // Only the exact overlay generated by the canonical, reviewed adapter
        // can authorize different bytes at this same path.
        f.write("adapted/tests/ui/a.rs", "fn main() {}");
        assert_eq!(f.outcomes(&tests, &log), [TestOutcome::Passed]);
        let roster = f.roster(&tests);
        f.write("adapted/tests/ui/a.rs", "fn main() { changed() }");
        assert_eq!(reconcile(&f.0, &roster, &parse_log(&log))[0].outcome, TestOutcome::Unknown);
    }

    #[test]
    fn preexisting_support_weakening_cannot_receive_pristine_pass_credit() {
        for path in [
            "tests/ui/auxiliary/support.rs",
            "tests/ui/a.stderr",
            "tests/run-make/example/data.bin",
        ] {
            let f = Fixture::new();
            let tests = [f.test("tests/ui/a.rs", "fn main() {}")];
            f.write(path, "weakened");
            f.write(&format!("pristine/{path}"), "original");
            f.write(&format!("adapted/{path}"), "original");
            let before = input_closure(&f.0);
            let admission = input_admission(&before, &f.0.join("pristine"), &f.0.join("adapted"));
            assert!(!admission.unresolved.is_empty(), "{path}");
            let log = f.0.join("execution.log");
            fs::write(&log, suite(&[("[ui] tests/ui/a.rs", "ok")])).unwrap();
            let proof = f.0.join("proof");
            super::super::write_execution_proof_artifacts(
                &f.0,
                &proof,
                &"1".repeat(40),
                &"2".repeat(40),
                &tests,
                0,
                &super::super::empty_trust_added_execution(&proof),
                &log,
                "bootstrap test",
                false,
                &super::super::empty_test_exception_ledger(),
                "2026-09-17",
                &f.roster(&tests),
                &before,
                &admission,
            )
            .unwrap();
            let results: serde_json::Value =
                serde_json::from_slice(&fs::read(proof.join("results.json")).unwrap()).unwrap();
            assert_eq!(results["results"][0]["outcome"], "unknown", "{path}");
            f.write(&format!("adapted/{path}"), "weakened");
            assert!(
                input_admission(&input_closure(&f.0), &f.0.join("pristine"), &f.0.join("adapted"))
                    .unresolved
                    .is_empty()
            );
        }
    }

    #[test]
    fn local_only_support_is_unresolved_but_reviewed_deletion_is_accounted() {
        let f = Fixture::new();
        f.test("tests/ui/a.rs", "fn main() {}");
        f.write("tests/ui/auxiliary/extra.rs", "fn extra() {}");
        assert!(
            !input_admission(&input_closure(&f.0), &f.0.join("pristine"), &f.0.join("adapted"))
                .unresolved
                .is_empty()
        );
        fs::remove_file(f.0.join("tests/ui/auxiliary/extra.rs")).unwrap();
        fs::remove_file(f.0.join("tests/ui/a.rs")).unwrap();
        fs::remove_file(f.0.join("adapted/tests/ui/a.rs")).unwrap();
        assert!(
            input_admission(&input_closure(&f.0), &f.0.join("pristine"), &f.0.join("adapted"))
                .unresolved
                .is_empty()
        );
        // The original row itself is still absent/Unknown, never a fabricated pass.
    }
}
