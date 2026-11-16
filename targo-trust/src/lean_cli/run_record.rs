// targo-trust/lean_cli/run_record.rs: the Lean lane's timing record,
// `trust.lean-run.v1` (edit-loop plan step 1, METER).
//
// Every `targo trust check <file.lean> …` writes
// `<target-dir>/trust/lean/<stem>-<16 hex>.json` beside the Rust lane's
// `trust/packages/` and `trust/obligations/` records, so `targo trust meter`
// reads one family under one directory. The target directory is the one
// every record of a `.lean` check goes under (`super::records::
// record_target_dir`): `--target-dir`, else `CARGO_TARGET_DIR`, else
// `CARGO_BUILD_TARGET_DIR`, else `target/` in the Cargo workspace root
// governing the current directory, where Cargo puts the Rust lane's records;
// outside every workspace with none of these set, the check writes no record
// and says so. The stem is the first operand's file stem; the hex is
// a digest of the operand set, so a rerun of the same invocation replaces its
// own record and no other.
//
// FORMAT. One JSON object, keys sorted at every level, one LF at the end:
//
//   {"cost":{"attempts":[{"check_us":…,"declarations":[{"automation_work":…,
//    "byte_start":…,"elapsed_us":…,"kind":"declaration|import|command",
//    "name":"…"}],"session_start_us":…|null}],"wall_clock_us":…},
//    "files":["…"],"outcome":"accepted|rejected","registered":["…"],
//    "schema":"trust.lean-run.v1","targo_trust_commit":"<40 hex>|unbound"}
//
// One `attempts` entry per kernel attempt of the import-closure fixpoint, in
// order. `session_start_us` is the fresh strict session's start (the kernel
// prelude and PProd prologue), `null` for an attempt refused before a session
// started; `declarations` are Clean's own per-declaration records
// (`clean_elab::DeclTiming`, a declaration's elaboration INCLUDING its kernel
// check as one span). Clean's module batch, which this lane runs, reaches that
// recorder only for lexical commands, so today `declarations` holds no
// `declaration` entry. `registered` names, sorted and distinct, the
// declarations the batch registered (each file verdict's head names: kernel
// accepted and admitted by Trust's island policy), so `targo trust meter`
// can say which of them no record times, rather than read an empty list as
// nothing elaborated or a count as coverage: a timed declaration the policy
// refused, or a nameless one, is no registered declaration's time.
// `wall_clock_us` is the whole batch. `files` are the operands as the caller
// wrote them.
//
// OBSERVATIONAL. Everything under `cost` is wall-clock time and varies from
// run to run; no verdict, digest or comparison reads this record. The verdict
// is the exit status and the per-file rows, as before.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use super::LeanRunTiming;

/// The schema name every Lean run record carries.
pub(crate) const LEAN_RUN_SCHEMA: &str = "trust.lean-run.v1";

/// The Lean run records directory of a target directory.
pub(crate) fn records_dir(target_dir: &Path) -> PathBuf {
    target_dir.join("trust").join("lean")
}

/// The record path of an invocation over `files` under `dir`.
pub(crate) fn record_path(dir: &Path, files: &[PathBuf]) -> PathBuf {
    let stem = files
        .first()
        .and_then(|file| file.file_stem())
        .map(|stem| crate::obligations::record_file_stem(&stem.to_string_lossy()))
        .unwrap_or_else(|| "lean".to_string());
    let mut keys: Vec<String> = files
        .iter()
        .map(|file| std::fs::canonicalize(file).unwrap_or_else(|_| file.clone()))
        .map(|file| file.display().to_string())
        .collect();
    keys.sort();
    keys.dedup();
    let mut hasher = Sha256::new();
    for key in &keys {
        hasher.update(key.as_bytes());
        hasher.update([0]);
    }
    let digest = hasher.finalize();
    let hex: String = digest.iter().take(8).map(|byte| format!("{byte:02x}")).collect();
    dir.join(format!("{stem}-{hex}.json"))
}

fn micros(duration: std::time::Duration) -> u64 {
    u64::try_from(duration.as_micros()).unwrap_or(u64::MAX)
}

fn kind_name(kind: clean_elab::DeclTimingKind) -> &'static str {
    match kind {
        clean_elab::DeclTimingKind::Import => "import",
        clean_elab::DeclTimingKind::Declaration => "declaration",
        // `Command` and any kind a later Clean adds: not a declaration, so
        // never charged to the elaborate-and-kernel-check phase.
        _ => "command",
    }
}

/// The `trust.lean-run.v1` bytes of one invocation.
pub(crate) fn render(
    files: &[PathBuf],
    accepted: bool,
    registered: &[String],
    timing: &LeanRunTiming,
) -> String {
    let mut registered = registered.to_vec();
    registered.sort();
    registered.dedup();
    let attempts: Vec<serde_json::Value> = timing
        .attempts
        .iter()
        .map(|attempt| {
            serde_json::json!({
                "session_start_us": attempt.session_start.map(micros),
                "check_us": micros(attempt.total),
                "declarations": attempt.declarations.iter().map(|declaration| serde_json::json!({
                    "name": declaration.name,
                    "kind": kind_name(declaration.kind),
                    "byte_start": declaration.byte_start,
                    "elapsed_us": micros(declaration.elapsed),
                    "automation_work": declaration.automation_work,
                })).collect::<Vec<_>>(),
            })
        })
        .collect();
    let value = serde_json::json!({
        "schema": LEAN_RUN_SCHEMA,
        "files": files.iter().map(|file| file.display().to_string()).collect::<Vec<_>>(),
        "outcome": if accepted { "accepted" } else { "rejected" },
        "registered": registered,
        "targo_trust_commit": crate::obligations::targo_trust_commit(),
        "cost": { "wall_clock_us": micros(timing.total), "attempts": attempts },
    });
    let mut bytes =
        trust_types::digest::canonical_json_bytes(&value).expect("a JSON value serializes");
    bytes.push(b'\n');
    String::from_utf8(bytes).expect("serde_json writes UTF-8")
}

/// Write the invocation's record under `target_dir`, atomically.
pub(crate) fn write(
    target_dir: &Path,
    files: &[PathBuf],
    accepted: bool,
    registered: &[String],
    timing: &LeanRunTiming,
) -> io::Result<PathBuf> {
    let path = record_path(&records_dir(target_dir), files);
    let bytes = render(files, accepted, registered, timing);
    crate::durable_io::atomic_write_private(&path, bytes.as_bytes())?;
    Ok(path)
}
