//! Input binding for the historical audit, never proof authority or a runner.

use std::collections::BTreeSet;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use serde_json::Value;

use super::bound_read;

pub(super) const CAPTURE_LIMIT: u64 = 8 * 1024 * 1024;
pub(super) const REPORT_LIMIT: u64 = 64 * 1024 * 1024;
pub(super) const SOURCE_LIMIT: u64 = 1024 * 1024;
const CASE_NAMES: [&str; 8] = [
    "baseline",
    "guarded",
    "disjunction",
    "baseline_whole_zero",
    "guarded_whole_zero",
    "disjunction_whole_zero",
    "guarded_floor_zero",
    "disjunction_floor_zero",
];
const HISTORICAL_ROWS: usize = 203;

pub(super) struct CapturedCase {
    pub(super) name: String,
    pub(super) report: PathBuf,
    pub(super) report_sha256: String,
    pub(super) source: PathBuf,
    pub(super) source_sha256: String,
    pub(super) rows: usize,
}

fn field<'a>(value: &'a Value, name: &str) -> Result<&'a str, String> {
    value[name]
        .as_str()
        .filter(|text| !text.is_empty())
        .ok_or_else(|| format!("missing or invalid capture field: {name}"))
}

pub(super) fn read_capture(path: &Path, digest: &str) -> Result<Vec<CapturedCase>, String> {
    let raw = bound_read(path, digest, CAPTURE_LIMIT)?;
    let capture: Value = serde_json::from_slice(&raw).map_err(|e| e.to_string())?;
    let cases = capture["cases"].as_array().ok_or("capture cases must be an array")?;
    if cases.len() != CASE_NAMES.len() {
        return Err("the complete original eight-case denominator is required".into());
    }
    let mut names = BTreeSet::new();
    let mut total = 0_usize;
    let mut bound = Vec::new();
    for case in cases {
        let name = field(case, "case")?;
        if !CASE_NAMES.contains(&name) || !names.insert(name) {
            return Err("the complete original eight-case denominator is required".into());
        }
        let directory = Path::new(field(case, "report_dir")?);
        let report = directory.join("report.json");
        let source = directory
            .parent()
            .and_then(Path::parent)
            .ok_or("capture report directory has no case source root")?
            .join("src/lib.rs");
        let report_sha256 = field(case, "report_sha256")?;
        let source_sha256 = field(case, "source_sha256")?;
        let report_raw = bound_read(&report, report_sha256, REPORT_LIMIT)?;
        bound_read(&source, source_sha256, SOURCE_LIMIT)?;
        let wire: Value = serde_json::from_slice(&report_raw).map_err(|e| e.to_string())?;
        let functions = wire["functions"].as_array().ok_or("report functions must be an array")?;
        let mut rows = 0_usize;
        for function in functions {
            let obligations =
                function["obligations"].as_array().ok_or("report obligations must be an array")?;
            rows = rows.checked_add(obligations.len()).ok_or("report row count overflow")?;
        }
        total = total.checked_add(rows).ok_or("capture row count overflow")?;
        bound.push(CapturedCase {
            name: name.into(),
            report,
            report_sha256: report_sha256.into(),
            source,
            source_sha256: source_sha256.into(),
            rows,
        });
    }
    if total != HISTORICAL_ROWS {
        return Err("the complete original 203-row denominator is required".into());
    }
    // Each report/source is read again by the audit before and after its checks.
    // The capture is similarly re-read here and after the complete audit.
    bound_read(path, digest, CAPTURE_LIMIT)?;
    Ok(bound)
}

pub(super) fn require_fresh_output(path: &Path) -> Result<(), String> {
    match fs::symlink_metadata(path) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error.to_string()),
        Ok(_) => Err("preserve previous output".into()),
    }
}

pub(super) fn write_fresh_output(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|e| e.to_string())?;
    file.write_all(bytes).map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use serde_json::json;

    use super::*;
    use crate::native_report_replay_tests::{bound_read_with_hooks, hash};

    struct Fixture {
        root: PathBuf,
        capture: Value,
    }

    impl Fixture {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let root = loop {
                let serial = NEXT.fetch_add(1, Ordering::Relaxed);
                let path = std::env::temp_dir()
                    .join(format!("trust-native-capture-{}-{serial}", std::process::id()));
                match fs::create_dir(&path) {
                    Ok(()) => break path,
                    Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("create owned fixture: {error}"),
                }
            };
            let mut cases = Vec::new();
            // Inert protocol rows with the real denominator; no proof claims.
            for (name, rows) in CASE_NAMES.into_iter().zip([25, 26, 25, 26, 25, 26, 25, 25]) {
                let case = root.join(name);
                let source = case.join("src/lib.rs");
                let directory = case.join("report/run");
                fs::create_dir_all(source.parent().unwrap()).unwrap();
                fs::create_dir_all(&directory).unwrap();
                let source_bytes = b"// inert protocol fixture, never executed\n";
                let report_bytes = serde_json::to_vec(&json!({
                    "functions": [{"obligations": vec![json!({}); rows]}]
                }))
                .unwrap();
                fs::write(&source, source_bytes).unwrap();
                fs::write(directory.join("report.json"), &report_bytes).unwrap();
                cases.push(json!({"case": name, "report_dir": directory,
                    "report_sha256": hash(&report_bytes), "source_sha256": hash(source_bytes)}));
            }
            Self { root, capture: json!({"cases": cases}) }
        }

        fn write_capture(&self, value: &Value) -> (PathBuf, String) {
            let bytes = serde_json::to_vec(value).unwrap();
            let path = self.root.join("results.json");
            fs::write(&path, &bytes).unwrap();
            (path, hash(&bytes))
        }

        fn report(&self) -> PathBuf {
            Path::new(self.capture["cases"][0]["report_dir"].as_str().unwrap()).join("report.json")
        }

        fn source(&self) -> PathBuf {
            self.root.join(CASE_NAMES[0]).join("src/lib.rs")
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.root).expect("remove only this fixture's owned directory");
        }
    }

    #[test]
    fn complete_capture_retains_all_cases_rows_and_original_order() {
        let fixture = Fixture::new();
        let mut capture = fixture.capture.clone();
        capture["cases"].as_array_mut().unwrap().reverse();
        let (path, digest) = fixture.write_capture(&capture);
        let cases = read_capture(&path, &digest).unwrap();
        assert_eq!(cases.iter().map(|case| case.rows).sum::<usize>(), HISTORICAL_ROWS);
        assert_eq!(
            cases.iter().map(|case| case.name.as_str()).collect::<Vec<_>>(),
            CASE_NAMES.into_iter().rev().collect::<Vec<_>>()
        );
    }

    #[test]
    fn malformed_duplicate_missing_and_unknown_cases_refuse() {
        let fixture = Fixture::new();
        for changed in [json!(null), json!({}), json!({"cases": {}})] {
            let (path, digest) = fixture.write_capture(&changed);
            assert!(read_capture(&path, &digest).is_err());
        }
        for change in ["missing", "duplicate", "unknown", "wrong-type", "missing-field"] {
            let mut capture = fixture.capture.clone();
            match change {
                "missing" => {
                    capture["cases"].as_array_mut().unwrap().pop();
                }
                "duplicate" => capture["cases"][0]["case"] = CASE_NAMES[1].into(),
                "unknown" => capture["cases"][0]["case"] = "foreign-case".into(),
                "wrong-type" => capture["cases"][0]["report_dir"] = json!(1),
                _ => {
                    capture["cases"][0].as_object_mut().unwrap().remove("source_sha256");
                }
            }
            let (path, digest) = fixture.write_capture(&capture);
            assert!(read_capture(&path, &digest).is_err(), "{change}");
        }
    }

    #[test]
    fn malformed_json_and_wrong_results_digest_refuse() {
        let fixture = Fixture::new();
        let (path, _) = fixture.write_capture(&fixture.capture);
        assert!(read_capture(&path, &"0".repeat(64)).is_err());
        fs::write(&path, b"{").unwrap();
        assert!(read_capture(&path, &hash(b"{")).is_err());
    }

    #[test]
    fn report_and_source_capture_mismatches_refuse() {
        for source in [false, true] {
            let fixture = Fixture::new();
            let (path, digest) = fixture.write_capture(&fixture.capture);
            fs::write(if source { fixture.source() } else { fixture.report() }, b"changed")
                .unwrap();
            assert!(read_capture(&path, &digest).is_err());
        }
    }

    #[test]
    fn malformed_report_and_reduced_row_denominator_refuse() {
        for malformed in [true, false] {
            let fixture = Fixture::new();
            let bytes = if malformed {
                serde_json::to_vec(&json!({"functions": [{"obligations": {}}]})).unwrap()
            } else {
                serde_json::to_vec(&json!({"functions": [{"obligations": []}]})).unwrap()
            };
            fs::write(fixture.report(), &bytes).unwrap();
            let mut capture = fixture.capture.clone();
            capture["cases"][0]["report_sha256"] = hash(&bytes).into();
            let (path, digest) = fixture.write_capture(&capture);
            assert!(read_capture(&path, &digest).is_err());
        }
    }

    #[test]
    fn oversized_capture_report_and_source_refuse() {
        for input in ["capture", "report", "source"] {
            let fixture = Fixture::new();
            let (path, digest) = fixture.write_capture(&fixture.capture);
            let (target, limit) = match input {
                "capture" => (path.clone(), CAPTURE_LIMIT),
                "report" => (fixture.report(), REPORT_LIMIT),
                _ => (fixture.source(), SOURCE_LIMIT),
            };
            fs::OpenOptions::new().write(true).open(target).unwrap().set_len(limit + 1).unwrap();
            assert!(read_capture(&path, &digest).is_err(), "{input}");
        }
    }

    #[cfg(unix)]
    #[test]
    fn symlink_capture_report_and_source_refuse() {
        for input in ["capture", "report", "source"] {
            let fixture = Fixture::new();
            let (path, digest) = fixture.write_capture(&fixture.capture);
            let target = match input {
                "capture" => path.clone(),
                "report" => fixture.report(),
                _ => fixture.source(),
            };
            let original = target.with_extension("preserved");
            fs::rename(&target, &original).unwrap();
            std::os::unix::fs::symlink(&original, &target).unwrap();
            assert!(read_capture(&path, &digest).is_err(), "{input}");
        }
    }

    #[test]
    fn replacement_between_stat_and_open_refuses_the_opened_identity() {
        let fixture = Fixture::new();
        let path = fixture.source();
        let digest = hash(&fs::read(&path).unwrap());
        assert!(bound_read(&path, &digest, SOURCE_LIMIT).is_ok());
        let result = bound_read_with_hooks(
            &path,
            &digest,
            SOURCE_LIMIT,
            || {
                fs::rename(&path, path.with_extension("preserved")).unwrap();
                fs::write(&path, b"replacement").unwrap();
            },
            || {},
        );
        assert!(result.unwrap_err().contains("identity changed before opening"));
    }

    #[cfg(unix)]
    #[test]
    fn replacement_to_symlink_is_refused_by_open_before_identity_checks() {
        let fixture = Fixture::new();
        let path = fixture.source();
        let digest = hash(&fs::read(&path).unwrap());
        let result = bound_read_with_hooks(
            &path,
            &digest,
            SOURCE_LIMIT,
            || {
                let original = path.with_extension("preserved");
                fs::rename(&path, &original).unwrap();
                std::os::unix::fs::symlink(&original, &path).unwrap();
            },
            || panic!("a swapped symlink must not reach the read boundary"),
        );
        assert_eq!(
            result.unwrap_err(),
            format!("input open refused: {}", nix::errno::Errno::ELOOP)
        );
    }

    #[cfg(unix)]
    #[test]
    fn replacement_to_fifo_is_refused_without_blocking() {
        const CHILD_PATH: &str = "TRUST_NATIVE_REPLAY_FIFO_CONTROL_PATH";
        if let Some(path) = std::env::var_os(CHILD_PATH) {
            let path = Path::new(&path);
            let digest = hash(&fs::read(path).unwrap());
            let result = bound_read_with_hooks(
                path,
                &digest,
                SOURCE_LIMIT,
                || {
                    fs::rename(path, path.with_extension("preserved")).unwrap();
                    nix::unistd::mkfifo(path, nix::sys::stat::Mode::S_IRUSR).unwrap();
                },
                || panic!("a swapped FIFO must not reach the read boundary"),
            );
            assert_eq!(result.unwrap_err(), "opened input is not a regular file");
            println!("swapped FIFO refused before reading");
            return;
        }

        // Re-execute only this control in the same test binary. If NONBLOCK
        // regresses, the parent kills/reaps its own child before removing the
        // owned fixture, rather than leaving a hung test or detached thread.
        let fixture = Fixture::new();
        let mut child = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "native_report_replay_tests::capture::tests::replacement_to_fifo_is_refused_without_blocking",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD_PATH, fixture.source())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        loop {
            let status = match child.try_wait() {
                Ok(status) => status,
                Err(error) => {
                    let _ = child.kill();
                    let _ = child.wait();
                    panic!("could not observe owned FIFO control child: {error}");
                }
            };
            if status.is_some() {
                let output = child.wait_with_output().unwrap();
                assert!(output.status.success(), "{output:?}");
                assert!(
                    String::from_utf8_lossy(&output.stdout)
                        .contains("swapped FIFO refused before reading"),
                    "zero executed controls cannot pass: {output:?}"
                );
                break;
            }
            if std::time::Instant::now() >= deadline {
                // The child may exit between the bounded poll and kill.
                let killed = child.kill();
                let output = child.wait_with_output().unwrap();
                panic!("swapped FIFO blocked before metadata rejection: {killed:?}; {output:?}");
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }

    #[test]
    fn growth_after_open_is_bounded_and_refused() {
        let fixture = Fixture::new();
        let path = fixture.source();
        fs::write(&path, b"original").unwrap();
        let result = bound_read_with_hooks(
            &path,
            &hash(b"original"),
            16,
            || {},
            || {
                fs::OpenOptions::new()
                    .append(true)
                    .open(&path)
                    .unwrap()
                    .write_all(&[b'x'; 1024])
                    .unwrap();
            },
        );
        assert!(result.is_err());
    }

    #[test]
    fn fresh_output_is_exclusive_even_after_an_earlier_freshness_check() {
        let fixture = Fixture::new();
        let output = fixture.root.join("audit.json");
        require_fresh_output(&output).unwrap();
        write_fresh_output(&output, b"preserved first output").unwrap();
        assert!(require_fresh_output(&output).is_err());
        assert!(write_fresh_output(&output, b"replacement").is_err());
        assert_eq!(fs::read(&output).unwrap(), b"preserved first output");
    }

    #[cfg(unix)]
    #[test]
    fn dangling_output_symlink_is_not_fresh() {
        let fixture = Fixture::new();
        let output = fixture.root.join("audit.json");
        std::os::unix::fs::symlink(fixture.root.join("absent"), &output).unwrap();
        assert!(require_fresh_output(&output).is_err());
        assert!(write_fresh_output(&output, b"replacement").is_err());
        assert!(fs::symlink_metadata(&output).unwrap().file_type().is_symlink());
    }
}
