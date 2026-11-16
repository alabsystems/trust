// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Observed compiler and recursive target-library bytes, not runtime attestation.

use std::error::Error;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};
use trust_stage_receipt::inventory::{DirectorySnapshot, EntryKind, Limits, capture_directory};

use super::{EXTRACTION_FLAGS, failure, file_sha256};

const SCHEMA: &str = "trust.source-compiler-observation/v2";
const LIBRARY_SCOPE: &str =
    "compiler-reported-target-libdir/recursive-directories-and-regular-files/v1";
const QUERY_LIMIT: usize = 64 * 1024;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct CompilerIdentity {
    pub(super) schema: String,
    pub(super) executable: PathBuf,
    pub(super) launcher_sha256: String,
    pub(super) version: Vec<u8>,
    version_stderr: Vec<u8>,
    pub(super) driver_files: Vec<(PathBuf, String)>,
    pub(super) target_library: TargetLibrary,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct LegacyCompilerIdentity {
    executable: PathBuf,
    launcher_sha256: String,
    version: Vec<u8>,
    driver_files: Vec<(PathBuf, String)>,
}

impl CompilerIdentity {
    pub(super) fn legacy_keys(&self) -> LegacyCompilerIdentity {
        LegacyCompilerIdentity {
            executable: self.executable.clone(),
            launcher_sha256: self.launcher_sha256.clone(),
            version: self.version.clone(),
            driver_files: self.driver_files.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct TargetLibrary {
    scope: String,
    query_stdout: Vec<u8>,
    query_stderr: Vec<u8>,
    root: PathBuf,
    entries: Vec<LibraryEntry>,
    total_bytes: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum LibraryEntry {
    Directory { path: String },
    File { path: String, bytes: u64, sha256: String },
}

fn target_directory(output: &[u8]) -> Result<PathBuf, Box<dyn Error>> {
    if output.len() > QUERY_LIMIT {
        return Err(failure("compiler target-library query exceeds its byte limit"));
    }
    let line = output
        .strip_suffix(b"\n")
        .ok_or("compiler target-library query has no final line terminator")?;
    let text = std::str::from_utf8(line)?;
    if text.is_empty()
        || text.len() > 4096
        || text.chars().any(|c| c.is_control() || matches!(c, '\u{fffd}' | '\u{2028}' | '\u{2029}'))
    {
        return Err(failure("compiler target-library query is empty, lossy or multiline"));
    }
    let path = PathBuf::from(text);
    if !path.is_absolute() {
        return Err(failure("compiler target-library query is not an absolute path"));
    }
    Ok(path)
}

fn library_record(
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    snapshot: DirectorySnapshot,
) -> Result<TargetLibrary, Box<dyn Error>> {
    let entries = snapshot
        .entries()
        .iter()
        .map(|entry| {
            let path =
                entry.relative_path().to_str().ok_or("inventory path is not UTF-8")?.to_owned();
            Ok(match entry.kind() {
                EntryKind::Directory => LibraryEntry::Directory { path },
                EntryKind::File { bytes, sha256 } => {
                    LibraryEntry::File { path, bytes: *bytes, sha256: sha256.clone() }
                }
            })
        })
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;
    Ok(TargetLibrary {
        scope: LIBRARY_SCOPE.to_owned(),
        query_stdout: stdout,
        query_stderr: stderr,
        root: snapshot.root().to_owned(),
        entries,
        total_bytes: snapshot.total_bytes(),
    })
}

/// Use the maintained bounded process owner; output remains exact bytes.
/// The runtime timeout is not an absolute OS or filesystem completion bound.
struct QueryOutput {
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

fn query(executable: &Path, cwd: &Path, arguments: &[&str]) -> Result<QueryOutput, Box<dyn Error>> {
    let mut process = cargo_util::ProcessBuilder::new(executable);
    process.cwd(cwd).args(arguments);
    let output = process.exec_with_streaming_limits(
        &mut |_| Ok(()),
        &mut |_| Ok(()),
        true,
        cargo_util::StreamingOutputLimits::new(QUERY_LIMIT, QUERY_LIMIT)
            .with_timeout(Duration::from_secs(30))
            .with_child_exit_cleanup(),
    )?;
    // The process owner enforces the same bound during collection, before this check.
    if output.stdout.len() > QUERY_LIMIT || output.stderr.len() > QUERY_LIMIT {
        return Err(failure("compiler identity query exceeds its byte limit"));
    }
    Ok(QueryOutput { stdout: output.stdout, stderr: output.stderr })
}

pub(super) fn compiler_identity(
    compiler: &Path,
    cwd: &Path,
) -> Result<CompilerIdentity, Box<dyn Error>> {
    capture_with(compiler, |executable, arguments| query(executable, cwd, arguments))
}

fn capture_with(
    compiler: &Path,
    mut query: impl FnMut(&Path, &[&str]) -> Result<QueryOutput, Box<dyn Error>>,
) -> Result<CompilerIdentity, Box<dyn Error>> {
    let started = Instant::now();
    eprintln!("phase compiler-identity started");
    // Preserve the existing canonical-executable argv0 policy. This is an
    // observation of selected bytes, not authentication of query truth.
    let executable = fs::canonicalize(compiler)?;
    let mut bounded_query = |arguments: &[&str]| -> Result<QueryOutput, Box<dyn Error>> {
        let output = query(&executable, arguments)?;
        if output.stdout.len() > QUERY_LIMIT || output.stderr.len() > QUERY_LIMIT {
            return Err(failure("compiler identity query exceeds its byte limit"));
        }
        Ok(output)
    };
    let version = bounded_query(&["--version", "--verbose"])?;
    let mut arguments = EXTRACTION_FLAGS.to_vec();
    arguments.extend(["--print", "target-libdir"]);
    let target = bounded_query(&arguments)?;
    let target_root = target_directory(&target.stdout)?;
    let snapshot = capture_directory(&target_root, Limits::default())?;
    let mut driver_files = Vec::new();
    let bin = executable.parent().ok_or("compiler has no parent")?;
    for folder in [bin.to_path_buf(), bin.join("../lib")] {
        if folder.is_dir() {
            for entry in fs::read_dir(&folder)? {
                let path = entry?.path();
                let name = path
                    .file_name()
                    .ok_or("driver has no leaf")?
                    .to_str()
                    .ok_or("driver name is not UTF-8")?;
                if name.starts_with("librustc_driver")
                    || name.starts_with("libtrustc_driver")
                    || name.starts_with("rustc_driver")
                    || name.starts_with("trustc_driver")
                {
                    if driver_files.len() >= 1024 {
                        return Err(failure("compiler driver inventory exceeds its entry limit"));
                    }
                    let path = fs::canonicalize(path)?;
                    driver_files.push((path.clone(), file_sha256(&path)?));
                }
            }
        }
    }
    driver_files.sort();
    driver_files.dedup();
    let identity = CompilerIdentity {
        schema: SCHEMA.to_owned(),
        launcher_sha256: file_sha256(&executable)?,
        executable,
        version: version.stdout,
        version_stderr: version.stderr,
        driver_files,
        target_library: library_record(target.stdout, target.stderr, snapshot)?,
    };
    eprintln!("phase compiler-identity finished elapsed_ms={}", started.elapsed().as_millis());
    Ok(identity)
}

#[cfg(test)]
pub(super) fn fixture() -> CompilerIdentity {
    CompilerIdentity {
        schema: SCHEMA.to_owned(),
        executable: PathBuf::from("/fixture/compiler"),
        launcher_sha256: "launcher".to_owned(),
        version: b"fixture version".to_vec(),
        version_stderr: vec![],
        driver_files: vec![(PathBuf::from("/fixture/driver"), "driver".to_owned())],
        target_library: TargetLibrary {
            scope: LIBRARY_SCOPE.to_owned(),
            query_stdout: b"/fixture/lib\n".to_vec(),
            query_stderr: vec![],
            root: PathBuf::from("/fixture/lib"),
            entries: vec![LibraryEntry::File {
                path: "libfixture.rmeta".to_owned(),
                bytes: 8,
                sha256: "0".repeat(64),
            }],
            total_bytes: 8,
        },
    }
}

#[cfg(all(test, unix))]
#[path = "identity/tests.rs"]
mod tests;
