//! The saved inputs of one run: its `run.json` and its published obligations.
//!
//! The obligation reader takes historical `trust.obligations.v1` records as
//! measurements, like the saved-audit comparator. It is not the proof-record
//! reader (`obligations::parse_package_ndjson`) and confers no grade.

use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::path::{Path, PathBuf};

use serde::Deserialize;
use serde_json::Value;
use sha2::{Digest as _, Sha256};

use super::Site;
use crate::audit_comparison::parse;
use crate::obligations::{TestCaseLine, TestHarnessLine};
use crate::test_results::CaseOutcome;

pub(crate) const RUN_SCHEMA: &str = "trust.seal-consumer-run.v1";
const OBLIGATIONS_SCHEMA: &str = "trust.obligations.v1";
pub(crate) const RUN_FILE: &str = "run.json";

/// One seal's run of one consumer's committed check command.
#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(crate) struct RunRecord {
    pub(crate) schema: String,
    pub(crate) consumer: String,
    /// The consumer's source: a full Git commit or tree id.
    pub(crate) tree: String,
    /// The literal command.
    pub(crate) command: String,
    /// The compiler commit of the seal that ran it.
    pub(crate) seal: String,
    pub(crate) cpus: u32,
    pub(crate) memory_gib: u32,
    /// The command ended, by itself or at its bound. An unfinished run is not
    /// compared.
    pub(crate) finished: bool,
    pub(crate) exit: i32,
    /// The run's wall-clock bound ended the command (COULD NOT RUN at the bound).
    #[serde(default)]
    pub(crate) stopped_at_bound: bool,
    /// The run's `trust.obligations.v1` records: a file or a directory, relative
    /// to the run directory unless absolute. Absent for a run that published none.
    #[serde(default)]
    pub(crate) obligations: Option<PathBuf>,
    /// The reds the command named, one per failing test or check.
    #[serde(default)]
    pub(crate) reds: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Row {
    pub(crate) site: Site,
    pub(crate) status: String,
    pub(crate) stop: String,
}

/// A finished run with the rows it published and a digest of every byte read.
#[derive(Clone, Debug)]
pub(crate) struct Run {
    pub(crate) record: RunRecord,
    pub(crate) rows: Vec<Row>,
    pub(crate) tests: BTreeMap<String, TestMeasurement>,
    pub(crate) digest: String,
}

/// A package's concluded libtest evidence. Ignored and executed cases are
/// separate populations even when they have the same names.
/// A package without authorized test harnesses can have an empty population.
#[derive(Clone, Debug, Default)]
pub(crate) struct TestMeasurement {
    arguments: Vec<String>,
    harnesses: BTreeSet<String>,
    cases: BTreeMap<String, CaseOutcome>,
}

impl TestMeasurement {
    pub(crate) fn population_matches(&self, other: &Self) -> bool {
        self.arguments == other.arguments
            && self.harnesses == other.harnesses
            && self.cases.iter().map(|(name, outcome)| (name, *outcome == CaseOutcome::Ignored)).eq(
                other.cases.iter().map(|(name, outcome)| (name, *outcome == CaseOutcome::Ignored)),
            )
    }

    pub(crate) fn failures(&self) -> impl Iterator<Item = &String> {
        self.cases
            .iter()
            .filter_map(|(name, outcome)| (*outcome == CaseOutcome::Failed).then_some(name))
    }

    pub(crate) fn failed(&self, case: &str) -> bool {
        self.cases.get(case) == Some(&CaseOutcome::Failed)
    }

    fn read(&mut self, row: Value) -> Result<(), String> {
        if row.get("test_harness").is_some() {
            let harness: TestHarnessLine = serde_json::from_value(row)
                .map_err(|error| format!("not a test-harness line: {error}"))?;
            if !harness.concluded || harness.reason.is_some() {
                return Err(format!(
                    "test harness {:?} did not report clean completion",
                    harness.test_harness
                ));
            }
            if harness.test_harness.trim().is_empty()
                || !self.harnesses.insert(harness.test_harness)
            {
                return Err("empty or repeated test harness".into());
            }
        } else {
            let case: TestCaseLine = serde_json::from_value(row)
                .map_err(|error| format!("not a test-case line: {error}"))?;
            if !case.test.split_once("::").is_some_and(|(harness, name)| {
                !name.trim().is_empty() && self.harnesses.contains(harness)
            }) {
                return Err(format!("test case {:?} names no known harness or case", case.test));
            }
            let Some(outcome) = CaseOutcome::parse(&case.outcome) else {
                return Err(format!(
                    "test case {:?} has an unknown outcome {:?}",
                    case.test, case.outcome
                ));
            };
            if outcome == CaseOutcome::NotConcluded {
                return Err(format!("test case {:?} has not concluded", case.test));
            }
            if self.cases.insert(case.test, outcome).is_some() {
                return Err("repeated test case".into());
            }
        }
        Ok(())
    }
}

/// What a run directory holds.
pub(crate) enum Loaded {
    Run(Box<Run>),
    /// No `run.json`, or one that says the run has not finished.
    Pending(String),
}

fn invalid(message: String) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

/// Read one run directory. A missing or unfinished run is `Pending`; anything
/// present and unreadable is an error, never an empty run.
pub(crate) fn load(directory: &Path) -> io::Result<Loaded> {
    let path = directory.join(RUN_FILE);
    let bytes = match parse::read_bytes(&path) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Ok(Loaded::Pending(format!("no {}", path.display())));
        }
        Err(error) => return Err(error),
    };
    let record: RunRecord = serde_json::from_slice(&bytes)
        .map_err(|error| invalid(format!("{}: {error}", path.display())))?;
    if record.schema != RUN_SCHEMA {
        return Err(invalid(format!(
            "{}: schema is {:?}, not {RUN_SCHEMA:?}",
            path.display(),
            record.schema
        )));
    }
    for (name, value) in [
        ("consumer", &record.consumer),
        ("tree", &record.tree),
        ("command", &record.command),
        ("seal", &record.seal),
    ] {
        if value.trim().is_empty() {
            return Err(invalid(format!("{}: {name} is empty", path.display())));
        }
    }
    if record.cpus == 0 || record.memory_gib == 0 {
        return Err(invalid(format!("{}: the budget names no CPU or no memory", path.display())));
    }
    if !record.finished {
        return Ok(Loaded::Pending(format!("{} says the run has not finished", path.display())));
    }
    if record.stopped_at_bound && record.exit == 0 {
        return Err(invalid(format!(
            "{}: a run stopped at its bound cannot have exited 0",
            path.display()
        )));
    }
    let mut hasher = Sha256::new();
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(&bytes);
    let mut tests = BTreeMap::new();
    let rows = match &record.obligations {
        None => Vec::new(),
        Some(relative) => {
            let root = directory.join(relative);
            let rows = read_obligations(&root, &mut hasher, &mut tests)?;
            if rows.is_empty() {
                return Err(invalid(format!(
                    "{}: names obligations at {}, which hold no {OBLIGATIONS_SCHEMA} obligation row",
                    path.display(),
                    root.display()
                )));
            }
            rows
        }
    };
    let digest = format!("sha256:{}", trust_types::digest::lowercase_hex(&hasher.finalize()));
    Ok(Loaded::Run(Box::new(Run { record, rows, tests, digest })))
}

fn read_obligations(
    root: &Path,
    hasher: &mut Sha256,
    tests: &mut BTreeMap<String, TestMeasurement>,
) -> io::Result<Vec<Row>> {
    let files = if root.is_dir() {
        parse::walk_files(root)?
            .into_iter()
            .filter(|path| path.extension().is_some_and(|extension| extension == "ndjson"))
            .collect::<Vec<_>>()
    } else {
        vec![root.to_owned()]
    };
    let mut rows = Vec::new();
    for path in files {
        let bytes = parse::read_bytes(&path)?;
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
        let text = std::str::from_utf8(&bytes)
            .map_err(|error| invalid(format!("{}: not UTF-8: {error}", path.display())))?;
        let mut lines = text.lines().enumerate();
        let Some((_, header)) = lines.next() else {
            return Err(invalid(format!("{}: empty obligations record", path.display())));
        };
        let header: Value = serde_json::from_str(header).map_err(|error| {
            invalid(format!("{}:1: not a JSON header: {error}", path.display()))
        })?;
        if header.get("schema").and_then(Value::as_str) != Some(OBLIGATIONS_SCHEMA) {
            return Err(invalid(format!(
                "{}:1: not a {OBLIGATIONS_SCHEMA} header",
                path.display()
            )));
        }
        // Early native v1 records predate the conclusion marker.
        match header.get("concluded") {
            None | Some(Value::Bool(true)) => {}
            Some(Value::Bool(false)) => {
                return Err(invalid(format!(
                    "{}: obligation measurement has not concluded",
                    path.display()
                )));
            }
            Some(_) => {
                return Err(invalid(format!("{}: concluded must be a boolean", path.display())));
            }
        }
        // A coverage row can arrive even when other units or functions are
        // missing. Older saved projections may omit the coverage field.
        match header.get("coverage_complete") {
            None | Some(Value::Bool(true)) => {}
            Some(Value::Bool(false)) => {
                return Err(invalid(format!(
                    "{}:1: obligation coverage is incomplete",
                    path.display()
                )));
            }
            Some(_) => {
                return Err(invalid(format!(
                    "{}:1: coverage_complete must be a boolean",
                    path.display()
                )));
            }
        }
        let package = header
            .get("package")
            .and_then(Value::as_str)
            .ok_or_else(|| invalid(format!("{}:1: the header names no package", path.display())))?
            .to_owned();
        let mut test_measurement = header
            .get("tests")
            .map(|arguments| {
                let arguments: Vec<String> =
                    serde_json::from_value(arguments.clone()).map_err(|error| {
                        invalid(format!("{}:1: invalid test arguments: {error}", path.display()))
                    })?;
                Ok::<_, io::Error>(TestMeasurement { arguments, ..TestMeasurement::default() })
            })
            .transpose()?;
        for (index, line) in lines {
            let number = index + 1;
            let row: Value = serde_json::from_str(line).map_err(|error| {
                invalid(format!("{}:{number}: not JSON: {error}", path.display()))
            })?;
            if row.get("test_harness").is_some() || row.get("test").is_some() {
                let measurement = test_measurement.as_mut().ok_or_else(|| {
                    invalid(format!("{}:{number}: test row without a test header", path.display()))
                })?;
                measurement
                    .read(row)
                    .map_err(|error| invalid(format!("{}:{number}: {error}", path.display())))?;
                continue;
            }
            // A function header row carries no obligation.
            if row.get("key").is_none() && row.get("fn").is_some() {
                continue;
            }
            let text = |name: &str| {
                row.get(name).and_then(Value::as_str).map(str::to_owned).ok_or_else(|| {
                    invalid(format!("{}:{number}: an obligation without {name}", path.display()))
                })
            };
            let key = text("key")?;
            let function =
                key.rsplit_once('#').map_or(key.as_str(), |(function, _)| function).to_owned();
            rows.push(Row {
                site: Site {
                    package: package.clone(),
                    function,
                    kind: text("kind")?,
                    // A row with no source position is still one obligation of
                    // its function and kind.
                    file: row.get("file").and_then(Value::as_str).unwrap_or("").to_owned(),
                    line: row.get("line").and_then(Value::as_u64).unwrap_or(0),
                    column: row.get("col").and_then(Value::as_u64).unwrap_or(0),
                },
                status: text("status")?,
                stop: text("stop")?,
            });
        }
        if let Some(measurement) = test_measurement {
            if tests.insert(package.clone(), measurement).is_some() {
                return Err(invalid(format!(
                    "{}: repeated test measurement for {package:?}",
                    path.display()
                )));
            }
        }
    }
    Ok(rows)
}
