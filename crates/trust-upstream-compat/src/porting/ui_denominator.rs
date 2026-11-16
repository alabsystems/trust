//! Pinned `tests/ui` input and case census. This is a diagnostic denominator,
//! not an authenticated execution channel or a release compatibility verdict.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use serde::Serialize;
use serde_json::{Value, json};

use super::observations::{self, Observation};
use super::{
    GitTreeEntry, PortError, TestInventory, TestKind, TestOutcome, TestResultReport, TestSource,
    git_command, run_capture,
};

const UI_PREFIX: &str = "tests/ui/";

#[derive(Debug, Clone, Serialize)]
pub(super) struct UiCase {
    pub id: String,
    pub path: String,
    pub source_git_blob: String,
}

#[derive(Debug)]
pub(super) struct UiRoster {
    pub revision: String,
    pub inputs: Vec<GitTreeEntry>,
    pub cases: Vec<UiCase>,
    pub test_paths: Vec<String>,
}

fn invalid(message: impl Into<String>) -> PortError {
    PortError::Message(format!("pinned tests/ui denominator: {}", message.into()))
}

fn parse_tree(output: &[u8]) -> Result<Vec<GitTreeEntry>, PortError> {
    if output.is_empty() || output.last() != Some(&0) {
        return Err(invalid("Git tree listing is empty or lacks NUL termination"));
    }
    let mut entries = Vec::new();
    let mut seen = BTreeSet::new();
    for record in output[..output.len() - 1].split(|byte| *byte == 0) {
        let record = std::str::from_utf8(record)
            .map_err(|_| invalid("Git tree contains a non-UTF-8 tests/ui path"))?;
        let (metadata, path) = record
            .split_once('\t')
            .ok_or_else(|| invalid("malformed NUL-delimited Git tree entry"))?;
        let parts = metadata.split_whitespace().collect::<Vec<_>>();
        if parts.len() != 4 {
            return Err(invalid(format!("malformed Git tree metadata for {path}")));
        }
        let [mode, kind, blob, size] = [parts[0], parts[1], parts[2], parts[3]];
        if !path.starts_with(UI_PREFIX)
            || path.bytes().any(|byte| matches!(byte, b'\n' | b'\r' | b'\\' | b'#'))
            || path.split('/').any(|part| part.is_empty() || part == "." || part == "..")
        {
            return Err(invalid(format!("unsupported Git tree path {path:?}")));
        }
        if !seen.insert(path.to_string()) {
            return Err(invalid(format!("duplicate Git tree path {path}")));
        }
        if kind != "blob" || !matches!(mode, "100644" | "100755") {
            return Err(invalid(format!("unsupported Git tree input kind {mode} {kind}: {path}")));
        }
        if !matches!(blob.len(), 40 | 64) || !blob.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(invalid(format!("invalid Git blob id for {path}")));
        }
        let size = size
            .parse::<u64>()
            .map_err(|_| invalid(format!("invalid Git blob size for {path}")))?;
        entries.push(GitTreeEntry {
            path: path.to_string(),
            mode: mode.to_string(),
            kind: kind.to_string(),
            blob: blob.to_string(),
            size: Some(size),
        });
    }
    entries.sort_by(|a, b| a.path.cmp(&b.path));
    Ok(entries)
}

fn test_paths(inputs: &[GitTreeEntry]) -> Vec<String> {
    let ignored = inputs
        .iter()
        .filter_map(|entry| entry.path.strip_suffix("/compiletest-ignore-dir").map(str::to_string))
        .collect::<BTreeSet<_>>();
    inputs
        .iter()
        .filter_map(|entry| {
            let path = entry.path.as_str();
            let filename = path.rsplit('/').next()?;
            if !filename.ends_with(".rs")
                || filename
                    .as_bytes()
                    .first()
                    .is_some_and(|byte| matches!(byte, b'.' | b'#' | b'~'))
                || path.strip_prefix(UI_PREFIX)?.split('/').any(|part| part == "auxiliary")
                || ignored.iter().any(|dir| path.starts_with(&format!("{dir}/")))
            {
                return None;
            }
            Some(path.to_string())
        })
        .collect()
}

fn archive_paths(root: &Path, dir: &Path, found: &mut BTreeSet<String>) -> Result<(), PortError> {
    for entry in fs::read_dir(dir).map_err(|error| {
        invalid(format!("cannot read pristine archive {}: {error}", dir.display()))
    })? {
        let entry =
            entry.map_err(|error| invalid(format!("cannot read archive entry: {error}")))?;
        let path = entry.path();
        let kind = entry
            .file_type()
            .map_err(|error| invalid(format!("cannot stat {}: {error}", path.display())))?;
        if kind.is_dir() {
            archive_paths(root, &path, found)?;
        } else if kind.is_file() {
            let relative = path
                .strip_prefix(root)
                .map_err(|_| invalid(format!("archive path escaped root: {}", path.display())))?
                .to_str()
                .ok_or_else(|| invalid(format!("non-UTF-8 archive path: {}", path.display())))?;
            found.insert(relative.to_string());
        } else {
            return Err(invalid(format!("unsupported pristine input: {}", path.display())));
        }
    }
    Ok(())
}

fn verify_pristine_inputs(pristine: &Path, inputs: &[GitTreeEntry]) -> Result<(), PortError> {
    let mut found = BTreeSet::new();
    archive_paths(pristine, &pristine.join("tests/ui"), &mut found)?;
    let expected = inputs.iter().map(|entry| entry.path.clone()).collect::<BTreeSet<_>>();
    if found != expected {
        let missing = expected.difference(&found).take(3).cloned().collect::<Vec<_>>();
        let extra = found.difference(&expected).take(3).cloned().collect::<Vec<_>>();
        return Err(invalid(format!(
            "pristine archive/Git tree path mismatch (missing {missing:?}, extra {extra:?})"
        )));
    }
    // One Git invocation per bounded chunk avoids both per-file process startup
    // and pipe deadlock while binding every support input, not only .rs cases.
    for chunk in inputs.chunks(500) {
        let output = git_command(pristine)
            .arg("hash-object")
            .arg("--")
            .args(chunk.iter().map(|entry| entry.path.as_str()))
            .output()
            .map_err(|error| invalid(format!("cannot hash pristine inputs: {error}")))?;
        if !output.status.success() {
            return Err(invalid(format!(
                "cannot hash pristine inputs: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            )));
        }
        let hashes = std::str::from_utf8(&output.stdout)
            .map_err(|_| invalid("git hash-object emitted non-UTF-8 output"))?
            .lines()
            .collect::<Vec<_>>();
        if hashes.len() != chunk.len() {
            return Err(invalid("git hash-object omitted one or more pristine inputs"));
        }
        for (entry, hash) in chunk.iter().zip(hashes) {
            if hash != entry.blob {
                return Err(invalid(format!(
                    "pristine blob mismatch for {}: tree={}, archive={hash}",
                    entry.path, entry.blob
                )));
            }
        }
    }
    Ok(())
}

impl UiRoster {
    pub fn load(root: &Path, revision: &str, pristine: &Path) -> Result<Self, PortError> {
        let tree = run_capture(
            root,
            "git",
            &["ls-tree", "-r", "-z", "-l", revision, "--", "tests/ui"],
            true,
        )?;
        let inputs = parse_tree(&tree)?;
        let test_paths = test_paths(&inputs);
        if test_paths.is_empty() {
            return Err(invalid("pinned tree has no independently discovered UI tests"));
        }
        verify_pristine_inputs(pristine, &inputs)?;
        let by_path =
            inputs.iter().map(|entry| (entry.path.as_str(), entry)).collect::<BTreeMap<_, _>>();
        let mut cases = Vec::new();
        let mut seen = BTreeSet::new();
        for path in &test_paths {
            let input = by_path[path.as_str()];
            let source = fs::read_to_string(pristine.join(path))
                .map_err(|error| invalid(format!("cannot read pinned UI test {path}: {error}")))?;
            let revisions = observations::revisions(&source).map_err(|error| {
                invalid(format!("cannot expand pinned UI test {path}: {error}"))
            })?;
            for revision in
                if revisions.is_empty() { vec![None] } else { revisions.iter().map(Some).collect() }
            {
                let id = match revision {
                    Some(revision) => format!("[ui] {path}#{revision}"),
                    None => format!("[ui] {path}"),
                };
                if !seen.insert(id.clone()) {
                    return Err(invalid(format!("duplicate pinned UI case {id}")));
                }
                cases.push(UiCase { id, path: path.clone(), source_git_blob: input.blob.clone() });
            }
        }
        Ok(Self { revision: revision.to_string(), inputs, cases, test_paths })
    }

    pub fn check_import_listing(&self, entries: &[GitTreeEntry]) -> Result<(), PortError> {
        let imported =
            entries.iter().filter(|entry| entry.path.starts_with(UI_PREFIX)).collect::<Vec<_>>();
        if imported.len() != self.inputs.len()
            || imported.iter().zip(&self.inputs).any(|(left, right)| {
                left.path != right.path
                    || left.blob != right.blob
                    || left.mode != right.mode
                    || left.kind != right.kind
            })
        {
            return Err(invalid(
                "legacy import listing differs from complete NUL-delimited pinned UI tree",
            ));
        }
        Ok(())
    }

    pub fn reconcile(&self, observed: &[Observation]) -> Value {
        let expected = self.cases.iter().map(|case| case.id.as_str()).collect::<BTreeSet<_>>();
        let mut by_id = BTreeMap::<&str, Vec<&Observation>>::new();
        for row in observed.iter().filter(|row| {
            row.path.starts_with(UI_PREFIX)
                || (row.name.starts_with("[ui] ")
                    && !row.path.starts_with("tests/ui-fulldeps/")
                    && !row.path.starts_with("tests/rustdoc-ui/"))
        }) {
            by_id.entry(&row.name).or_default().push(row);
        }
        let mut diagnostics = Vec::new();
        let mut case_results = Vec::with_capacity(self.cases.len());
        for case in &self.cases {
            let rows = by_id.get(case.id.as_str()).map_or(&[][..], Vec::as_slice);
            if rows.is_empty() {
                diagnostics.push(format!("missing executed UI case: {}", case.id));
            } else if rows.len() != 1 {
                diagnostics.push(format!(
                    "duplicate executed UI case: {} ({})",
                    case.id,
                    rows.len()
                ));
            } else if !rows[0].complete_suite {
                diagnostics.push(format!("incomplete renderer suite for UI case: {}", case.id));
            }
            let outcome = if rows.len() == 1 && rows[0].complete_suite {
                rows[0].outcome
            } else {
                TestOutcome::Unknown
            };
            case_results.push(json!({
                "id": case.id,
                "outcome": outcome,
                "observation_count": rows.len(),
            }));
        }
        for (id, rows) in &by_id {
            if !expected.contains(id) {
                diagnostics.push(format!(
                    "generated-path, revision, or mode mismatch: {id} ({} observation(s))",
                    rows.len()
                ));
            }
        }
        json!({
            "schema": "trust.upstream-rust.ui-denominator.v1",
            "surface": "tests/ui",
            "upstream_revision": self.revision,
            "release_status": "unknown",
            "release_status_reason": "terminal records are not authenticated execution events",
            "roster_complete": true,
            "observations_reconciled": diagnostics.is_empty(),
            "inputs": self.inputs,
            "cases": self.cases,
            "case_results": case_results,
            "diagnostics": diagnostics,
        })
    }

    pub fn validate_artifact(
        &self,
        artifact: &Value,
        inventory: &TestInventory,
        results: &TestResultReport,
    ) -> Result<(), String> {
        if artifact["schema"] != "trust.upstream-rust.ui-denominator.v1"
            || artifact["upstream_revision"] != self.revision
            || inventory.upstream_revision != self.revision
            || artifact["release_status"] != "unknown"
            || artifact["roster_complete"] != true
            || artifact["observations_reconciled"] != true
            || artifact["diagnostics"].as_array().is_none_or(|items| !items.is_empty())
            || artifact["inputs"] != json!(self.inputs)
            || artifact["cases"] != json!(self.cases)
        {
            return Err(
                "UI denominator artifact does not match pinned tree or has unresolved observations"
                    .into(),
            );
        }
        let ui_tests = inventory
            .tests
            .iter()
            .filter(|test| test.path.starts_with(UI_PREFIX))
            .collect::<Vec<_>>();
        if inventory
            .tests
            .iter()
            .any(|test| test.suite == "ui" && !test.path.starts_with(UI_PREFIX))
        {
            return Err("UI inventory contains a generated path outside tests/ui".into());
        }
        let by_path =
            ui_tests.iter().map(|test| (test.path.as_str(), *test)).collect::<BTreeMap<_, _>>();
        if ui_tests.len() != self.test_paths.len() || by_path.len() != self.test_paths.len() {
            return Err(
                "UI inventory has omissions, duplicate paths, or generated test paths".into()
            );
        }
        let tree_blobs = self
            .inputs
            .iter()
            .map(|entry| (entry.path.as_str(), entry.blob.as_str()))
            .collect::<BTreeMap<_, _>>();
        for path in &self.test_paths {
            let Some(test) = by_path.get(path.as_str()) else {
                return Err(format!("UI inventory omitted pinned test {path}"));
            };
            if test.source != TestSource::UpstreamRust
                || test.kind != TestKind::Compiletest
                || test.suite != "ui"
                || test.source_git_blob.as_deref() != tree_blobs.get(path.as_str()).copied()
            {
                return Err(format!("UI inventory identity/blob mismatch for {path}"));
            }
        }
        let case_results = artifact["case_results"]
            .as_array()
            .ok_or_else(|| "UI case results are missing".to_string())?;
        if case_results.len() != self.cases.len() {
            return Err("UI case results omit or add pinned cases".into());
        }
        let mut all_pass_by_path = BTreeMap::<&str, bool>::new();
        for (case, result) in self.cases.iter().zip(case_results) {
            if result["id"] != case.id || result["observation_count"] != 1 {
                return Err(format!(
                    "UI case result omitted, duplicated, or reordered: {}",
                    case.id
                ));
            }
            let outcome = serde_json::from_value::<TestOutcome>(result["outcome"].clone())
                .map_err(|_| format!("invalid UI case outcome for {}", case.id))?;
            let all_pass = all_pass_by_path.entry(&case.path).or_insert(true);
            *all_pass &= outcome == TestOutcome::Passed;
        }
        let result_by_id = results
            .results
            .iter()
            .map(|result| (result.test_id.as_str(), result))
            .collect::<BTreeMap<_, _>>();
        let inventory_ids =
            inventory.tests.iter().map(|test| test.id.as_str()).collect::<BTreeSet<_>>();
        if results.results.len() != inventory.tests.len()
            || result_by_id.len() != inventory.tests.len()
            || result_by_id.keys().copied().collect::<BTreeSet<_>>() != inventory_ids
        {
            return Err("proof results omit, duplicate, or add inventory test IDs".into());
        }
        for (path, test) in by_path {
            // This target-independent roster cannot authenticate an upstream
            // directive or host decision that removes a pinned UI test.
            if !test.applicable || test.inapplicable_reason.is_some() {
                return Err(format!(
                    "UI inventory has unauthenticated target applicability for {path}"
                ));
            }
            let result = result_by_id
                .get(test.id.as_str())
                .ok_or_else(|| format!("UI proof result omitted pinned test {path}"))?;
            if result.outcome == TestOutcome::UpstreamInapplicable {
                return Err(format!(
                    "UI proof result has unauthenticated target inapplicability for {path}"
                ));
            }
            if result.outcome == TestOutcome::Passed
                && !all_pass_by_path.get(path).copied().unwrap_or(false)
            {
                return Err(format!(
                    "UI file result passes despite a non-passing pinned case: {path}"
                ));
            }
        }
        Ok(())
    }
}

pub(super) fn write_failure(
    path: &Path,
    revision: &str,
    error: &PortError,
) -> Result<(), PortError> {
    let diagnostic = json!({
        "schema": "trust.upstream-rust.ui-denominator.v1",
        "surface": "tests/ui",
        "upstream_revision": revision,
        "release_status": "unknown",
        "roster_complete": false,
        "observations_reconciled": false,
        "diagnostics": [error.to_string()],
    });
    let bytes = serde_json::to_vec_pretty(&diagnostic)?;
    fs::create_dir_all(path.parent().unwrap()).map_err(PortError::Io)?;
    fs::write(path, bytes).map_err(PortError::Io)
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::process::{Command, Stdio};
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;
    use crate::{TestInventoryEntry, TestResult};

    struct Fixture(PathBuf);

    impl Fixture {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let root = std::env::temp_dir().join(format!(
                "trust-ui-denominator-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&root).unwrap();
            let fixture = Self(root);
            fixture.git(&["init", "-q"]);
            fixture.write("tests/ui/a.rs", "//@ revisions: first second\nfn main() {}\n");
            fixture.write("tests/ui/nested/b.rs", "fn main() {}\n");
            fixture.write("tests/ui/nested/auxiliary/helper.rs", "pub fn helper() {}\n");
            fixture.write("tests/ui/ignored/compiletest-ignore-dir", "");
            fixture.write("tests/ui/ignored/not-a-test.rs", "fn main() {}\n");
            fixture.write("tests/ui/.temporary.rs", "fn main() {}\n");
            fixture.write("tests/ui/a.stderr", "expected diagnostic\n");
            fixture.git(&["add", "tests/ui"]);
            fixture.git(&[
                "-c",
                "user.name=Trust Test",
                "-c",
                "user.email=trust@example.invalid",
                "commit",
                "-qm",
                "fixture",
            ]);
            fixture
        }

        fn git(&self, args: &[&str]) -> String {
            let output = Command::new("git").args(args).current_dir(&self.0).output().unwrap();
            assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
            String::from_utf8(output.stdout).unwrap()
        }

        fn write(&self, path: &str, contents: &str) {
            let path = self.0.join(path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, contents).unwrap();
        }

        fn roster(&self) -> UiRoster {
            UiRoster::load(&self.0, self.git(&["rev-parse", "HEAD"]).trim(), &self.0).unwrap()
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }

    fn log(names: &[&str]) -> String {
        let mut log = format!("running {} tests\n", names.len());
        for name in names {
            log.push_str(&format!("test {name} ... ok\n"));
        }
        log.push_str(&format!(
            "test result: ok. {} passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n",
            names.len()
        ));
        log
    }

    fn proof(roster: &UiRoster) -> (TestInventory, TestResultReport) {
        let by_path = roster
            .inputs
            .iter()
            .map(|entry| (entry.path.as_str(), entry))
            .collect::<BTreeMap<_, _>>();
        let inventory = TestInventory {
            schema_version: crate::SCHEMA_VERSION.into(),
            upstream_revision: roster.revision.clone(),
            local_revision: "b".repeat(40),
            host: None,
            tests: roster
                .test_paths
                .iter()
                .enumerate()
                .map(|(index, path)| TestInventoryEntry {
                    id: format!("upstream.{index:08}.{}", path.replace('/', ".")),
                    suite: "ui".into(),
                    path: path.clone(),
                    revision: Some(roster.revision.clone()),
                    source_git_blob: Some(by_path[path.as_str()].blob.clone()),
                    source: TestSource::UpstreamRust,
                    kind: TestKind::Compiletest,
                    applicable: true,
                    inapplicable_reason: None,
                    source_sha256: None,
                })
                .collect(),
        };
        let results = TestResultReport {
            schema_version: crate::SCHEMA_VERSION.into(),
            inventory_id: "fixture".into(),
            generated_on: "2026-09-24".into(),
            command: "bootstrap test".into(),
            results: inventory
                .tests
                .iter()
                .map(|test| TestResult {
                    test_id: test.id.clone(),
                    outcome: TestOutcome::Passed,
                    exception_id: None,
                    observed: None,
                    artifact: None,
                })
                .collect(),
        };
        (inventory, results)
    }

    #[test]
    fn pinned_tree_includes_support_inputs_but_only_compiletest_ui_cases() {
        let fixture = Fixture::new();
        let roster = fixture.roster();
        assert_eq!(roster.inputs.len(), 7);
        assert_eq!(roster.test_paths, ["tests/ui/a.rs", "tests/ui/nested/b.rs"]);
        assert_eq!(
            roster.cases.iter().map(|case| case.id.as_str()).collect::<Vec<_>>(),
            ["[ui] tests/ui/a.rs#first", "[ui] tests/ui/a.rs#second", "[ui] tests/ui/nested/b.rs",]
        );
        let observations = observations::parse_log(&log(&[
            "[ui] tests/ui/a.rs#first",
            "[ui] tests/ui/a.rs#second",
            "[ui] tests/ui/nested/b.rs",
        ]));
        let artifact = roster.reconcile(&observations);
        assert_eq!(artifact["release_status"], "unknown");
        assert_eq!(artifact["observations_reconciled"], true);
        let (inventory, results) = proof(&roster);
        roster.validate_artifact(&artifact, &inventory, &results).unwrap();
        let other_ui_suites = format!(
            "{}{}{}",
            log(&[
                "[ui] tests/ui/a.rs#first",
                "[ui] tests/ui/a.rs#second",
                "[ui] tests/ui/nested/b.rs",
            ]),
            log(&["[ui] tests/ui-fulldeps/other.rs"]),
            log(&["[ui] tests/rustdoc-ui/other.rs"]),
        );
        assert_eq!(
            roster.reconcile(&observations::parse_log(&other_ui_suites))["observations_reconciled"],
            true
        );
    }

    #[test]
    fn missing_duplicate_and_generated_cases_fail_exact_reconciliation() {
        let fixture = Fixture::new();
        let roster = fixture.roster();
        for (names, diagnostic) in [
            (
                vec!["[ui] tests/ui/a.rs#first", "[ui] tests/ui/nested/b.rs"],
                "missing executed UI case",
            ),
            (
                vec![
                    "[ui] tests/ui/a.rs#first",
                    "[ui] tests/ui/a.rs#first",
                    "[ui] tests/ui/a.rs#second",
                    "[ui] tests/ui/nested/b.rs",
                ],
                "duplicate executed UI case",
            ),
            (
                vec![
                    "[ui] tests/ui/a.rs#first",
                    "[ui] tests/ui/a.rs#second",
                    "[ui] tests/ui/nested/b.rs",
                    "[ui] tests/ui/generated.rs",
                ],
                "generated-path",
            ),
            (
                vec![
                    "[ui] tests/ui/a.rs#first",
                    "[ui] tests/ui/a.rs#second",
                    "[ui] tests/ui/nested/b.rs",
                    "[ui] build/generated.rs",
                ],
                "generated-path",
            ),
            (
                vec![
                    "[ui] tests/ui/a.rs#first",
                    "[ui] tests/ui/a.rs#second",
                    "[ui] tests/ui/nested/b.rs",
                    "[ui] tests/generated.rs",
                ],
                "generated-path",
            ),
            (
                vec![
                    "[ui] tests/ui/a.rs#first",
                    "[ui] tests/ui/a.rs#third",
                    "[ui] tests/ui/nested/b.rs",
                ],
                "revision",
            ),
        ] {
            let artifact = roster.reconcile(&observations::parse_log(&log(&names)));
            assert_eq!(artifact["observations_reconciled"], false);
            assert!(artifact["diagnostics"].to_string().contains(diagnostic));
            let (inventory, results) = proof(&roster);
            assert!(roster.validate_artifact(&artifact, &inventory, &results).is_err());
        }
    }

    #[test]
    fn missing_or_substituted_inputs_and_results_cannot_shrink_denominator() {
        let fixture = Fixture::new();
        let roster = fixture.roster();
        let artifact = roster.reconcile(&observations::parse_log(&log(&[
            "[ui] tests/ui/a.rs#first",
            "[ui] tests/ui/a.rs#second",
            "[ui] tests/ui/nested/b.rs",
        ])));
        let (mut inventory, results) = proof(&roster);
        inventory.tests.pop();
        assert!(roster.validate_artifact(&artifact, &inventory, &results).is_err());
        let (mut inventory, results) = proof(&roster);
        inventory.tests[0].path = "tests/ui/generated.rs".into();
        assert!(roster.validate_artifact(&artifact, &inventory, &results).is_err());
        let (mut inventory, results) = proof(&roster);
        inventory.tests[0].path = "tests/generated.rs".into();
        assert!(roster.validate_artifact(&artifact, &inventory, &results).is_err());
        let (mut inventory, results) = proof(&roster);
        inventory.tests[0].source_git_blob = Some("0".repeat(40));
        assert!(roster.validate_artifact(&artifact, &inventory, &results).is_err());
        let (mut inventory, results) = proof(&roster);
        inventory.upstream_revision = "0".repeat(40);
        assert!(roster.validate_artifact(&artifact, &inventory, &results).is_err());
        let (inventory, mut results) = proof(&roster);
        let mut bad_artifact = artifact.clone();
        bad_artifact["upstream_revision"] = json!("0".repeat(40));
        assert!(roster.validate_artifact(&bad_artifact, &inventory, &results).is_err());
        let mut bad_artifact = artifact.clone();
        bad_artifact["case_results"].as_array_mut().unwrap().pop();
        assert!(roster.validate_artifact(&bad_artifact, &inventory, &results).is_err());
        let mut bad_artifact = artifact.clone();
        bad_artifact["case_results"][0]["outcome"] = json!("skipped");
        assert!(roster.validate_artifact(&bad_artifact, &inventory, &results).is_err());
        results.results.pop();
        assert!(roster.validate_artifact(&artifact, &inventory, &results).is_err());
    }

    #[test]
    fn ui_target_inapplicability_cannot_replace_observed_cases() {
        let fixture = Fixture::new();
        fixture
            .write("tests/ui/a.rs", "//@ revisions: first second\n//@ only-x86_64\nfn main() {}\n");
        fixture.git(&["add", "tests/ui/a.rs"]);
        fixture.git(&[
            "-c",
            "user.name=Trust Test",
            "-c",
            "user.email=trust@example.invalid",
            "commit",
            "-qm",
            "target-scoped fixture",
        ]);
        let roster = fixture.roster();
        let artifact = roster.reconcile(&observations::parse_log(&log(&[
            "[ui] tests/ui/a.rs#first",
            "[ui] tests/ui/a.rs#second",
            "[ui] tests/ui/nested/b.rs",
        ])));

        for host in ["x86_64-unknown-linux-gnu", "aarch64-apple-darwin"] {
            let (mut inventory, results) = proof(&roster);
            inventory.host = Some(host.into());
            roster.validate_artifact(&artifact, &inventory, &results).unwrap();

            for (applicable, outcome) in [
                (false, TestOutcome::Passed),
                (false, TestOutcome::UpstreamInapplicable),
                (true, TestOutcome::UpstreamInapplicable),
            ] {
                let (mut inventory, mut results) = proof(&roster);
                inventory.host = Some(host.into());
                inventory.tests[0].applicable = applicable;
                inventory.tests[0].inapplicable_reason =
                    (!applicable).then(|| "only-x86_64".into());
                results.results[0].outcome = outcome;
                let error = roster.validate_artifact(&artifact, &inventory, &results).unwrap_err();
                assert!(error.contains("unauthenticated target"), "{host}: {error}");
            }
        }
    }

    #[test]
    fn archive_and_tree_mismatches_return_failing_diagnostic() {
        let fixture = Fixture::new();
        let revision = fixture.git(&["rev-parse", "HEAD"]);
        fixture.write("tests/ui/a.stderr", "weakened expected diagnostic\n");
        let error = UiRoster::load(&fixture.0, revision.trim(), &fixture.0).unwrap_err();
        assert!(error.to_string().contains("pristine blob mismatch"));
        let diagnostic = fixture.0.join("ui-denominator.json");
        write_failure(&diagnostic, revision.trim(), &error).unwrap();
        let value: Value = serde_json::from_slice(&fs::read(diagnostic).unwrap()).unwrap();
        assert_eq!(value["release_status"], "unknown");
        assert_eq!(value["roster_complete"], false);
        fixture.write("tests/ui/generated.rs", "fn main() {}\n");
        let error = UiRoster::load(&fixture.0, revision.trim(), &fixture.0).unwrap_err();
        assert!(error.to_string().contains("archive/Git tree path mismatch"));
    }

    #[test]
    fn malformed_or_ambiguous_tree_entries_are_rejected() {
        let blob = "a".repeat(40);
        let entry = format!("100644 blob {blob} 1\ttests/ui/a.rs\0");
        assert!(parse_tree(entry.as_bytes()).is_ok());
        assert!(parse_tree(entry.trim_end_matches('\0').as_bytes()).is_err());
        assert!(parse_tree(format!("{entry}{entry}").as_bytes()).is_err());
        assert!(
            parse_tree(format!("120000 blob {blob} 1\ttests/ui/link.rs\0").as_bytes()).is_err()
        );
        assert!(
            parse_tree(format!("100644 blob {blob} 1\ttests/ui/a#rev.rs\0").as_bytes()).is_err()
        );
    }

    #[test]
    fn replacement_ref_cannot_shrink_revision_tree_or_exported_inputs() {
        let fixture = Fixture::new();
        let original = fixture.git(&["rev-parse", "HEAD"]);
        let original = original.trim();
        fs::remove_file(fixture.0.join("tests/ui/nested/b.rs")).unwrap();
        fixture.git(&["add", "-A", "tests/ui"]);
        fixture.git(&[
            "-c",
            "user.name=Trust Test",
            "-c",
            "user.email=trust@example.invalid",
            "commit",
            "-qm",
            "smaller replacement",
        ]);
        let replacement = fixture.git(&["rev-parse", "HEAD"]);
        fixture.git(&["replace", original, replacement.trim()]);

        let spoofed = Command::new("git")
            .args(["ls-tree", "-r", "--name-only", original, "--", "tests/ui"])
            .env_remove("GIT_NO_REPLACE_OBJECTS")
            .current_dir(&fixture.0)
            .output()
            .unwrap();
        assert!(spoofed.status.success());
        assert!(!String::from_utf8(spoofed.stdout).unwrap().contains("tests/ui/nested/b.rs"));

        let entries = super::super::list_upstream_tests(&fixture.0, original).unwrap();
        assert!(entries.iter().any(|entry| entry.path == "tests/ui/nested/b.rs"));
        let imported = fixture.0.join("imported");
        super::super::export_overlay(&fixture.0, original, &entries, &imported, None).unwrap();
        assert!(imported.join("tests/ui/nested/b.rs").is_file());
        let roster = UiRoster::load(&fixture.0, original, &imported).unwrap();
        assert_eq!(roster.test_paths, ["tests/ui/a.rs", "tests/ui/nested/b.rs"]);
    }

    #[test]
    #[ignore = "requires the locally fetched pinned rust-lang/rust object"]
    fn pinned_upstream_ui_tree_expands_without_narrowing() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap();
        let pin = "5e91de65d75d3c849c643f5079509b9e5985a5c0";
        let temp = std::env::temp_dir().join(format!("trust-pinned-ui-{}", std::process::id()));
        fs::create_dir(&temp).unwrap();
        let mut archive = Command::new("git")
            .args(["archive", "--format=tar", pin, "tests/ui"])
            .current_dir(root)
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let extract = Command::new("tar")
            .args(["-xf", "-", "-C"])
            .arg(&temp)
            .stdin(Stdio::from(archive.stdout.take().unwrap()))
            .status()
            .unwrap();
        assert!(extract.success());
        assert!(archive.wait().unwrap().success());
        let roster = UiRoster::load(root, pin, &temp).unwrap();
        eprintln!(
            "pinned UI denominator: {} inputs, {} test files, {} cases",
            roster.inputs.len(),
            roster.test_paths.len(),
            roster.cases.len()
        );
        assert!(roster.inputs.len() > 30_000);
        assert!(roster.test_paths.len() > 15_000);
        assert!(roster.cases.len() >= roster.test_paths.len());
        fs::remove_dir_all(temp).unwrap();
    }
}
