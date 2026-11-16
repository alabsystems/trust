//! The `trust.obligations.v1` record of a `.lean` check: one row for the
//! file's verdict and one per declaration, keyed by its stable name
//! (`trust_types::lean_declaration_identity`), so a Lean file's results are
//! compared and diffed (`crate::agent_delta`) exactly as a crate's are.
//!
//! The commands, where each starts and their canonical names are Clean's own
//! (`trust_certify::clean_island::CleanIslandOutcome::declarations`); nothing
//! here reads the file's command structure. A declaration's text, which its
//! statement anchor and source digest are read from, runs from its keyword to
//! the line the next listed command starts on. A row's status is read from the
//! check's verdict, never computed here:
//!
//! * `proved` (stopped `solved`) only when the WHOLE batch was accepted
//!   (`CheckedLeanBatch::accepted_context`): every file accepted, the publish
//!   audit and the reference kernel recheck passed, the batch committed. For a
//!   `def`, `structure` or `instance` row (its kind says which) that is the
//!   kernel accepting the definition, which is its only obligation here;
//! * `failed` for a declaration something refused (Clean, Trust's
//!   registered-declaration policy, the reference recheck, the publish audit
//!   naming it — a `sorry` it reaches — or a cycle), and for the file row of a
//!   file the check REJECTED with an elaborator or kernel error. Its proof was
//!   rejected; nothing refuted its statement. So it is stopped
//!   `solver-incomplete` (`StopCause::SolverIncomplete`, whose vocabulary
//!   names a certification refusal), never `solved`, the stop a decided
//!   verdict — a Rust refutation — carries, and its basis is
//!   `unproved_fail_closed`, which the listing and the changed-only view print
//!   as `FAILED: unproved, no counterexample; failed closed`;
//! * `unknown`, stopped `unsupported`, for a file that imports a module Clean
//!   served from a prelude stand-in (checked only against the stand-in) and its
//!   declarations;
//! * otherwise `unknown`, stopped `not-dispatched`: the batch was refused
//!   (here or in a sibling file), so it registered nothing and the final
//!   acceptance checks did not run for this declaration.
//!
//! A file Clean could not parse has only its file row, and a file the batch
//! never elaborated (`could-not-run`) the same; neither record is
//! `coverage_complete`, and no record with an `unknown` row is.
//!
//! Every row is ungraded: the grade axes are the compiler's statement, and the
//! Lean lane states none.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};
use trust_certify::clean_island::CleanIslandOutcome;
use trust_types::lean_declaration_identity::{
    lean_command_texts, lean_declaration_id, lean_declarations,
};
use trust_types::obligation_identity::obligation_key;

use super::{CheckedLeanBatch, FileVerdict, line_and_column};
use crate::obligations::{
    FunctionRecords, ObligationRecord, PackageRecords, RecordHeader, UNGRADED,
    render_package_ndjson,
};

/// The lane, policy and selection a `.lean` check's record states: the Lean
/// lane has one lane and no selection flags.
const LEAN_LANE: &str = "strict";
const LEAN_SELECTION: &str = "default";
/// The Lean lane runs no budgeted search, so it has no budget profile.
const LEAN_PROFILE: &str = "none";
/// The def path of the file's own row. Not a Lean identifier, so no
/// declaration can take it.
pub(super) const FILE_ROW: &str = "<file>";

/// The status and stop of a row whose proof was rejected (module docs).
const PROOF_REJECTED: (&str, &str) = ("failed", "solver-incomplete");

/// The target directory of every record a `.lean` check writes — its
/// `trust.obligations.v1` records and snapshots here, its
/// `trust.lean-run.v1` timing record (`super::run_record`) — and the one a
/// bare `targo trust meter` reads: `--target-dir`, else Cargo's
/// `CARGO_TARGET_DIR`, else `CARGO_BUILD_TARGET_DIR`, else `target/` in the
/// Cargo workspace root that governs the current directory
/// (`config::workspace_root_dir`, the directory whose `target/` a crate-mode
/// check writes its records under). Run from a workspace subdirectory, both
/// lanes and the meter name the same directory. A `build.target-dir` in a
/// Cargo config file is not read here.
///
/// `Ok(None)` outside every workspace with none of these set: the caller then
/// writes nothing rather than a `target/` directory wherever it was run, and
/// says so ([`NO_TARGET_DIR`]). `Err` when the current directory cannot be
/// read or `config::workspace_root_dir` fails.
pub(crate) fn record_target_dir(explicit: Option<&Path>) -> Result<Option<PathBuf>, String> {
    record_target_dir_in(explicit, std::env::current_dir)
}

/// [`record_target_dir`] with `cwd` reading the current directory, which is
/// read only when neither `--target-dir` nor the environment names one.
pub(super) fn record_target_dir_in(
    explicit: Option<&Path>,
    cwd: impl FnOnce() -> std::io::Result<PathBuf>,
) -> Result<Option<PathBuf>, String> {
    if let Some(dir) = explicit {
        return Ok(Some(dir.to_path_buf()));
    }
    for name in ["CARGO_TARGET_DIR", "CARGO_BUILD_TARGET_DIR"] {
        if let Some(dir) = std::env::var_os(name).filter(|value| !value.is_empty()) {
            return Ok(Some(PathBuf::from(dir)));
        }
    }
    let cwd = cwd().map_err(|error| format!("cannot read the current directory: {error}"))?;
    let root = crate::config::workspace_root_dir(&cwd).map_err(|error| {
        format!("cannot find the workspace whose target directory holds the records: {error}")
    })?;
    Ok(root.map(|root| root.join("target")))
}

/// Why a `.lean` check outside every workspace wrote no record.
pub(crate) const NO_TARGET_DIR: &str = "no record written: no --target-dir, CARGO_TARGET_DIR or \
     CARGO_BUILD_TARGET_DIR, and no Cargo workspace at or above the current directory; pass \
     --target-dir DIR to keep this run's records";

/// The record file of the `.lean` file `package` (its canonical path) under
/// `target_dir`: its file name and a digest of the whole path, so two files
/// never share a record file.
pub(super) fn record_path(target_dir: &Path, package: &str) -> PathBuf {
    let name = Path::new(package)
        .file_name()
        .map_or_else(|| "lean".to_string(), |name| name.to_string_lossy().into_owned());
    crate::obligations::obligation_record_path(
        &crate::obligations::records_dir(target_dir),
        &format!("{name}-{}", crate::agent_delta::token_of(package.as_bytes())),
    )
}

/// `(package, record bytes)` for every file of the batch whose source was
/// read. The package is the file's canonical path: one record per file.
pub(super) fn file_records(checked: &CheckedLeanBatch) -> Vec<(String, String)> {
    let batch_accepted = checked.accepted_context().is_some();
    let outcomes = checked.outcomes();
    checked
        .sources()
        .iter()
        .zip(checked.verdicts())
        .enumerate()
        .filter_map(|(index, (source, verdict))| {
            let text = source.source().ok()?;
            let package = std::fs::canonicalize(verdict.path())
                .unwrap_or_else(|_| verdict.path().to_path_buf())
                .display()
                .to_string();
            let outcome = outcomes.and_then(|outcomes| outcomes.get(index));
            Some((package.clone(), file_record(&package, verdict, outcome, batch_accepted, text)))
        })
        .collect()
}

/// The status and stop of the file's own row (module docs).
fn file_status(
    verdict: &FileVerdict,
    outcome: Option<&CleanIslandOutcome>,
    batch_accepted: bool,
) -> (&'static str, &'static str) {
    if batch_accepted {
        ("proved", "solved")
    } else if verdict.accepted() {
        ("unknown", "not-dispatched")
    } else if outcome.is_some_and(CleanIslandOutcome::is_rejected) {
        PROOF_REJECTED
    } else if !verdict.standin_imports.is_empty() {
        ("unknown", "unsupported")
    } else {
        ("unknown", "not-dispatched")
    }
}

/// The status and stop of one declaration (module docs).
fn declaration_status(
    verdict: &FileVerdict,
    refused: bool,
    batch_accepted: bool,
) -> (&'static str, &'static str) {
    if refused {
        PROOF_REJECTED
    } else if batch_accepted {
        ("proved", "solved")
    } else if !verdict.standin_imports.is_empty() {
        ("unknown", "unsupported")
    } else {
        ("unknown", "not-dispatched")
    }
}

fn record(
    key: String,
    kind: String,
    (status, stop): (&str, &str),
    file: &str,
    (line, col): (usize, usize),
) -> ObligationRecord {
    ObligationRecord {
        key,
        kind,
        status: status.to_string(),
        stop: stop.to_string(),
        file: Some(file.to_string()),
        line: u32::try_from(line).ok(),
        col: u32::try_from(col).ok(),
        encoding: UNGRADED.to_string(),
        discharge: UNGRADED.to_string(),
        premises: Vec::new(),
        // A rejected proof refutes nothing: the row fails closed.
        basis: (status == trust_types::Outcome::Failed.as_str())
            .then(|| trust_types::FailureBasis::UnprovedFailClosed.as_str().to_string()),
    }
}

fn file_record(
    package: &str,
    verdict: &FileVerdict,
    outcome: Option<&CleanIslandOutcome>,
    batch_accepted: bool,
    text: &str,
) -> String {
    let file = verdict.path().display().to_string();
    let mut functions: PackageRecords = BTreeMap::new();
    let file_id = lean_declaration_id("file", "", 0);
    functions.entry(FILE_ROW.to_string()).or_default().obligations.insert(
        file_id.clone(),
        record(
            obligation_key(FILE_ROW, &file_id),
            "lean:file".to_string(),
            file_status(verdict, outcome, batch_accepted),
            &file,
            (1, 1),
        ),
    );
    let commands = outcome.and_then(|outcome| outcome.declarations.as_deref());
    // Clean's span of a command is its keyword; its text runs from there to
    // the line the next command Clean lists starts on (the end of the file for
    // the last), which leaves that command's attributes and `set_option … in`
    // to it. A span outside the text is a command this record cannot read
    // (and the record is then not complete), never a guess.
    let listed = commands.unwrap_or_default();
    let spans: Vec<(usize, usize)> =
        listed.iter().map(|command| (command.start, command.end)).collect();
    let readable: Vec<_> = listed
        .iter()
        .zip(lean_command_texts(text, &spans))
        .filter_map(|(command, source)| Some((command, source?)))
        .collect();
    let all_read = readable.len() == commands.map_or(0, <[_]>::len);
    let named = lean_declarations(
        readable.iter().map(|(command, source)| (command.name.as_deref(), *source)),
    );
    let mut per_name: BTreeMap<&str, usize> = BTreeMap::new();
    for declaration in named.iter().flatten() {
        *per_name.entry(declaration.name.as_str()).or_default() += 1;
    }
    for ((command, _), declaration) in readable.iter().zip(&named) {
        let Some(declaration) = declaration else { continue };
        let function = functions.entry(declaration.name.clone()).or_insert_with(|| {
            FunctionRecords {
                // A def path several declarations share (`example`) has no one
                // source digest.
                source: (per_name[declaration.name.as_str()] == 1)
                    .then(|| declaration.source_digest.clone()),
                obligations: BTreeMap::new(),
            }
        });
        function.obligations.insert(
            declaration.local_id.clone(),
            record(
                declaration.key(),
                format!("lean:{}", declaration.keyword.replace(' ', "-")),
                declaration_status(verdict, command.refused, batch_accepted),
                &file,
                line_and_column(text, command.start),
            ),
        );
    }
    let rows = || functions.values().flat_map(|function| function.obligations.values());
    let mut vector = Sha256::new();
    for record in rows() {
        vector.update(format!("{}\t{}\n", record.key, record.status).as_bytes());
    }
    let vector: String = vector.finalize().iter().map(|b| format!("{b:02x}")).collect();
    let coverage_complete =
        commands.is_some() && all_read && rows().all(|record| record.status != "unknown");
    let commit = crate::obligations::targo_trust_commit();
    let header = RecordHeader {
        package,
        lane: LEAN_LANE,
        policy: LEAN_LANE,
        selection: LEAN_SELECTION,
        targo_trust_commit: &commit,
        profile: LEAN_PROFILE,
        outcome: if outcome.is_some() { "measured" } else { "could-not-run" },
        vector: &vector,
        coverage_complete,
        // The file row states the file's verdict whatever it is, so every
        // `.lean` record is compared (`crate::obligations`, CONCLUDED): a
        // refused batch's undecided declarations print as LOST.
        concluded: true,
        degraded_anchors: 0,
    };
    render_package_ndjson(&header, &functions)
}

#[cfg(test)]
#[path = "records_tests.rs"]
mod tests;
