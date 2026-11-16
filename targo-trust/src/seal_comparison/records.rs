//! The saved inputs of one run: its `run.json` and its published obligations.
//!
//! The obligation reader takes historical `trust.obligations.v1` records as
//! measurements, like the saved-audit comparator. It is not the proof-record
//! reader (`obligations::parse_package_ndjson`) and confers no grade.

use std::io;
use std::path::{Path, PathBuf};

use serde::Deserialize;
use serde_json::Value;
use sha2::{Digest as _, Sha256};

use super::Site;
use crate::audit_comparison::parse;

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
    pub(crate) digest: String,
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
    let rows = match &record.obligations {
        None => Vec::new(),
        Some(relative) => {
            let root = directory.join(relative);
            let rows = read_obligations(&root, &mut hasher)?;
            if rows.is_empty() {
                return Err(invalid(format!(
                    "{}: names obligations at {}, which hold no {OBLIGATIONS_SCHEMA} row",
                    path.display(),
                    root.display()
                )));
            }
            rows
        }
    };
    let digest = format!("sha256:{}", trust_types::digest::lowercase_hex(&hasher.finalize()));
    Ok(Loaded::Run(Box::new(Run { record, rows, digest })))
}

fn read_obligations(root: &Path, hasher: &mut Sha256) -> io::Result<Vec<Row>> {
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
        let package = header
            .get("package")
            .and_then(Value::as_str)
            .ok_or_else(|| invalid(format!("{}:1: the header names no package", path.display())))?
            .to_owned();
        for (index, line) in lines {
            let number = index + 1;
            let row: Value = serde_json::from_str(line).map_err(|error| {
                invalid(format!("{}:{number}: not JSON: {error}", path.display()))
            })?;
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
    }
    Ok(rows)
}
