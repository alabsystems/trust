// targo-trust/agent_delta.rs: changed-only results for the editing agent
// (live-edit-loop plan, step 2 DELTA; docs/design/2026-11-12-live-edit-loop.md).
//
// A check writes each package's `trust.obligations.v1` record
// (`crate::obligations`). This module keeps those records as SNAPSHOTS,
// content-addressed under `<target-dir>/trust/snapshots/<token>`, where the
// token is the first sixteen hex digits of the SHA-256 of the record's bytes —
// the whole record: every obligation's key, kind, status, stop, location and
// grade, and the header's facts, not only the proved keys a baseline holds.
// Equal tokens are equal records.
//
// A run is compared with a BASE snapshot and prints only the rows that
// changed, in the baseline's row words (`crate::baseline`), plus one summary
// line per package:
//
//   <package>  N of M changed since <old>  (now <new>)
//
// The base is the snapshot `--since <token>` names, or else the last token
// this CALLER was given for this package and measurement (lane, policy,
// selection). The caller is the agent session the environment names
// (`ATERM_SESSION_ID`, set by aterm in every tab, and `CLAUDE_CODE_SESSION_ID`,
// set by Claude Code); its pointer files live under
// `snapshots/callers/<caller digest>/`, so agents sharing one target directory
// never diff against each other's runs. With no caller and no `--since` there
// is no base and the output is today's full listing.
//
// What changed: a row is compared by its key, status, stop, grade (encoding,
// discharge, premises) and failure basis — everything the listing's label and
// the record say about it — but not by its location, so lines inserted above
// a function change no row (N stays 0), while the summary line names the new
// token, since the record, and so its token, carries every row's location. A
// grade or basis change with the same status is a `CHANGED` row. A header
// fact that moved (outcome, coverage, the targo-trust commit, the profile) is
// a `RUN` line. `N` counts the obligation rows that changed; a `RUN` line is
// not one.
//
// What is never hidden: a row the listing does not label a plain `PROVED` —
// failed, runtime-checked, unknown, timed out, assumed, contract, conditional
// — prints on every run. Where the command prints a per-row listing of its own
// (a crate-mode `targo trust check`), the view narrows that listing rather
// than replacing it: the listing's own line of every such row stays, with its
// message, location and backend, whether or not the row has a stable key or
// belongs to a package the view covers (`crate::report`, `terminal_lines_with`),
// and the view adds only what changed. Where it prints none (a `.lean` check,
// `targo trust delta`), such a row unchanged prints as a `STILL` row. Either
// way a reader of the output is never told less about a row that is not
// plainly proved than the listing would tell them. `N` does not count those
// rows. Each view row carries the listing's own label for it
// (`ObligationRecord::listing_label`: `[FAILED: …]`, `[ASSUMED]`,
// `[RUNTIME-CHECKED]`, …).
//
// Compiler errors are rows too. A package with an error-level compiler
// diagnostic (a compile error, or the verifier's own refusal) carries one
// error line per error in its record (`crate::obligations`), keyed by file,
// error code and normalized message, never by line, so an edit elsewhere in
// the file keeps the key. They are compared with the caller's previous
// snapshot, whatever it measured: a new one is `NEW ERROR`, one no longer
// reported `CLEARED`, and, since no listing prints them, every one still
// reported prints on every run (`STILL`, or with no base the row alone).
//
// Whether a record's obligations are compared is decided by what its unit
// published, never by whether it reported an error: a record is compared
// only when it concluded (its header's `concluded`: a unit of the package
// published its coverage row). A package with a refused obligation reports
// the verifier's error and concluded, so its rows are compared as any other
// run's, `LOST` and `VANISHED` rows included. A record that did not conclude
// (the package did not compile, its unit never reached its coverage row, or a
// dependency did not compile so it was never built) measured no obligation:
// its obligations are not compared (its header facts are, and with no
// listing of the command's own its rows not plainly proved print as `STILL`),
// and its summary line is `<package>  K compiler error(s); obligations not
// compared since <old>  (now <new>)`, or `not concluded` in place of the
// count when it reported none. The obligations' base is the caller's last
// snapshot that concluded (a second pointer, `<pointer>.concluded`, which
// only a concluded run moves), so after a fix the view is the `CLEARED` rows
// and whatever changed since the last run that concluded. A package that
// reported an error is in the view whether or not the run selected it (a
// dependency that did not compile). The verdict, the gate lines and the exit
// status are the run's own, as before: a package that did not compile is
// `could-not-run`.
//
// The caller is a session, not an agent: subagents and workflow workers that
// share one session's environment and one target directory share its
// pointers. Separate target directories (one per worktree) keep them apart.
//
// Snapshots and pointers are observational: a write failure is a note, never a
// verdict or an exit status, and no verdict is read from a snapshot — the run's
// own gate and `Summary:` lines decide. A snapshot whose bytes do not hash to
// its name, or a pointer that does not name a token, is refused (a note, and no
// base). A snapshot nobody read or wrote for 7 days is removed when a new
// snapshot is written.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use sha2::{Digest, Sha256};
use trust_types::obligation_identity::split_obligation_key;

use crate::baseline::{BaselineFunction, pair_functions};
use crate::obligations::{
    CompileErrorRecord, FunctionRecords, ObligationRecord, PackageObligations, PackageRecords,
    parse_package_ndjson,
};

/// The environment variables that name the calling agent session, in order.
/// Every one that is set joins the caller's identity.
pub(crate) const CALLER_SESSION_ENV: [&str; 2] = ["ATERM_SESSION_ID", "CLAUDE_CODE_SESSION_ID"];

/// How long an unread snapshot or caller pointer is kept.
pub(crate) const SNAPSHOT_RETENTION: Duration = Duration::from_secs(7 * 24 * 60 * 60);

/// The number of hex digits in a token.
const TOKEN_HEX_LEN: usize = 16;

/// What the caller asked for.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct DeltaRequest {
    /// `--since <token>`: the base snapshot.
    pub(crate) since: Option<String>,
    /// `--all-rows`: print every row as well as the changes.
    pub(crate) all_rows: bool,
}

impl DeltaRequest {
    /// Take `--since <token>` / `--since=<token>` and `--all-rows` out of
    /// `args` (before any `--`), leaving everything else in order.
    pub(crate) fn take_from(args: &mut Vec<String>) -> Result<Self, String> {
        let mut request = Self::default();
        let mut index = 0;
        while index < args.len() {
            match args[index].as_str() {
                "--" => break,
                "--all-rows" => {
                    request.all_rows = true;
                    args.remove(index);
                }
                "--since" => {
                    args.remove(index);
                    if index >= args.len() || args[index].starts_with('-') {
                        return Err("--since requires a snapshot token".to_string());
                    }
                    request.since = Some(args.remove(index));
                }
                arg if arg.starts_with("--since=") => {
                    let value = arg.strip_prefix("--since=").expect("prefix checked").to_string();
                    args.remove(index);
                    request.since = Some(value);
                }
                _ => index += 1,
            }
        }
        if let Some(token) = &request.since {
            if !is_token(token) {
                return Err(format!(
                    "--since takes a snapshot token ({TOKEN_HEX_LEN} lowercase hex digits, as a \
                     check prints it), not `{token}`"
                ));
            }
        }
        Ok(request)
    }
}

/// The caller session named by the environment, or `None`.
pub(crate) fn caller_session_from_env() -> Option<String> {
    let parts: Vec<String> = CALLER_SESSION_ENV
        .iter()
        .filter_map(|name| {
            std::env::var(name)
                .ok()
                .filter(|value| !value.is_empty())
                .map(|v| format!("{name}={v}"))
        })
        .collect();
    (!parts.is_empty()).then(|| parts.join("\0"))
}

fn sha16(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    digest[..TOKEN_HEX_LEN / 2].iter().map(|b| format!("{b:02x}")).collect()
}

/// The token of a record's bytes.
pub(crate) fn token_of(bytes: &[u8]) -> String {
    sha16(bytes)
}

fn is_token(text: &str) -> bool {
    text.len() == TOKEN_HEX_LEN
        && text.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// `<target-dir>/trust/snapshots`.
pub(crate) fn snapshots_dir(target_dir: &Path) -> PathBuf {
    target_dir.join("trust").join("snapshots")
}

/// The caller pointer of `package` measured as `lane`/`policy`/`selection`.
fn pointer_path(dir: &Path, caller: &str, record: &PackageObligations) -> PathBuf {
    let measurement =
        format!("{}\0{}\0{}\0{}", record.package, record.lane, record.policy, record.selection);
    dir.join("callers").join(sha16(caller.as_bytes())).join(sha16(measurement.as_bytes()))
}

/// Mark `path` as used now, so retention counts from this read.
fn touch(path: &Path) {
    if let Ok(file) = std::fs::OpenOptions::new().write(true).open(path) {
        let _ = file.set_modified(SystemTime::now());
    }
}

/// Remove every snapshot and caller pointer under `dir` last used more than
/// [`SNAPSHOT_RETENTION`] ago, except `keep`. Returns how many were removed.
fn prune(dir: &Path, keep: &Path, now: SystemTime) -> usize {
    let stale = |path: &Path| {
        path != keep
            && std::fs::metadata(path).and_then(|meta| meta.modified()).is_ok_and(|modified| {
                now.duration_since(modified).unwrap_or_default() > SNAPSHOT_RETENTION
            })
    };
    let mut removed = 0;
    let Ok(entries) = std::fs::read_dir(dir) else {
        return 0;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().into_owned();
        if is_token(&name) && path.is_file() && stale(&path) {
            removed += usize::from(std::fs::remove_file(&path).is_ok());
        }
    }
    let callers = dir.join("callers");
    for caller in std::fs::read_dir(&callers).into_iter().flatten().flatten() {
        let caller = caller.path();
        for pointer in std::fs::read_dir(&caller).into_iter().flatten().flatten() {
            let pointer = pointer.path();
            if pointer.is_file() && stale(&pointer) {
                removed += usize::from(std::fs::remove_file(&pointer).is_ok());
            }
        }
        let _ = std::fs::remove_dir(&caller);
    }
    removed
}

/// Store `bytes` as a snapshot and return its token. An existing snapshot of
/// the same token whose bytes hash to it is the same record and is only marked
/// used; any other is (re)written, and writing a new one first removes the
/// stale ones.
fn store(dir: &Path, bytes: &[u8]) -> std::io::Result<String> {
    let token = token_of(bytes);
    let path = dir.join(&token);
    if std::fs::read(&path).is_ok_and(|held| token_of(&held) == token) {
        touch(&path);
    } else {
        std::fs::create_dir_all(dir)?;
        crate::durable_io::atomic_write_private(&path, bytes)?;
        prune(dir, &path, SystemTime::now());
    }
    Ok(token)
}

/// Read the snapshot `token`, marking it used. Its bytes must hash to its
/// name: a snapshot is content-addressed, so one that does not is not the
/// record the token names, and is refused.
fn load(dir: &Path, token: &str) -> Option<Result<PackageObligations, String>> {
    if !is_token(token) {
        return Some(Err(format!("`{token}` is not a snapshot token")));
    }
    let path = dir.join(token);
    if !path.is_file() {
        return None;
    }
    touch(&path);
    let text = match crate::input_limits::read_bounded_utf8_file(
        &path,
        crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES,
    ) {
        Ok(text) => text,
        Err(error) => return Some(Err(format!("cannot read `{}`: {error}", path.display()))),
    };
    let actual = token_of(text.as_bytes());
    if actual != token {
        return Some(Err(format!(
            "`{}` holds bytes whose token is {actual}, not {token}; refused",
            path.display()
        )));
    }
    Some(parse_package_ndjson(&text).map_err(|error| format!("`{}`: {error}", path.display())))
}

/// One package's place in a delta.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PackageDelta {
    pub(crate) package: String,
    /// The obligation rows of this run.
    pub(crate) total: usize,
    /// The compiler errors of this run.
    pub(crate) compile_errors: usize,
    /// Whether this run's record concluded (`crate::obligations`,
    /// CONCLUDED): only then were its obligations compared.
    pub(crate) concluded: bool,
    /// This run's token, when its snapshot was stored.
    pub(crate) now: Option<String>,
    /// The base token and what changed since it, when there was a base.
    pub(crate) since: Option<(String, Changes)>,
    /// The compile-error rows against the previous snapshot (`error_rows`):
    /// no listing prints them, so the view does on every run.
    pub(crate) errors: Vec<String>,
    /// Every row of this run, for `--all-rows` where the command prints no
    /// listing of its own (a `.lean` check, `targo trust delta`).
    pub(crate) all: Vec<String>,
}

impl PackageDelta {
    /// `<package>  N of M changed since <old>  (now <new>)`, or, with no base,
    /// `<package>  M obligation(s)  (now <new>)`; a package that reported
    /// compiler errors leads with `K compiler error(s); `. A package whose
    /// record did not conclude says so instead of a count it did not
    /// measure: `<package>  K compiler error(s); obligations not compared
    /// since <old>  (now <new>)`, with `not concluded` in place of the count
    /// when it reported no error (a dependency did not compile).
    pub(crate) fn summary_line(&self) -> String {
        let now = self.now.as_deref().unwrap_or("not stored");
        let package = &self.package;
        let errors = self.compile_errors;
        let lead = if errors > 0 {
            format!("{errors} compiler error(s); ")
        } else if !self.concluded {
            "not concluded; ".to_string()
        } else {
            String::new()
        };
        match &self.since {
            Some((old, _)) if !self.concluded => {
                format!("{package}  {lead}obligations not compared since {old}  (now {now})")
            }
            Some((old, changes)) => format!(
                "{package}  {lead}{} of {} changed since {old}  (now {now})",
                changes.rows, self.total
            ),
            None => format!("{package}  {lead}{} obligation(s)  (now {now})", self.total),
        }
    }
}

/// What a run tells the agent: per package, its changed rows and summary.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct DeltaView {
    pub(crate) packages: Vec<PackageDelta>,
    /// Why a base was not used, or a snapshot not stored.
    pub(crate) notes: Vec<String>,
    pub(crate) all_rows: bool,
}

impl DeltaView {
    /// Whether the changed rows replace the run's full listing: every package
    /// had a base and `--all-rows` was not given.
    pub(crate) fn replaces_listing(&self) -> bool {
        !self.all_rows
            && !self.packages.is_empty()
            && self.packages.iter().all(|package| package.since.is_some())
    }

    /// The lines to print: the notes, then per package its changed rows (and,
    /// with `--all-rows`, every row first) and its summary line.
    pub(crate) fn lines(&self) -> Vec<String> {
        let mut lines: Vec<String> =
            self.notes.iter().map(|note| format!("note: {note}")).collect();
        for package in &self.packages {
            lines.extend(package.errors.iter().cloned());
            lines.extend(package.all.iter().cloned());
            if let Some((_, changes)) = &package.since {
                lines.extend(changes.lines.iter().cloned());
            }
            lines.push(package.summary_line());
        }
        lines
    }
}

/// Snapshot each `(package, record bytes)` under `target_dir`, compare it with
/// its base and move the caller's pointer to it.
pub(crate) fn publish(
    target_dir: &Path,
    records: &[(String, String)],
    request: &DeltaRequest,
    caller: Option<&str>,
    list_rows: bool,
) -> DeltaView {
    let dir = snapshots_dir(target_dir);
    let mut view = DeltaView { all_rows: request.all_rows, ..DeltaView::default() };
    // `--since` names one package's snapshot.
    let since = request.since.as_deref().and_then(|token| match load(&dir, token) {
        Some(Ok(record)) => Some((token.to_string(), record)),
        Some(Err(error)) => {
            view.notes.push(format!("snapshot {token} cannot be read ({error}); no base"));
            None
        }
        None => {
            view.notes.push(format!(
                "snapshot {token} is not under {} (removed after 7 days unused, or written to \
                 another target directory); no base",
                dir.display()
            ));
            None
        }
    });
    if let Some((token, base)) = &since {
        if !records.iter().any(|(package, _)| *package == base.package) {
            view.notes.push(format!(
                "snapshot {token} is package `{}`, which this run did not record",
                base.package
            ));
        }
    }
    for (package, bytes) in records {
        let now = match parse_package_ndjson(bytes) {
            Ok(now) => now,
            Err(error) => {
                view.notes.push(format!("the record of `{package}` cannot be read back: {error}"));
                continue;
            }
        };
        let pointer = caller.map(|caller| pointer_path(&dir, caller, &now));
        let concluded_pointer = pointer.as_ref().map(|pointer| pointer.with_extension("concluded"));
        let base = match &since {
            Some((token, base)) if base.package == *package => Some((token.clone(), base.clone())),
            _ => pointer
                .as_ref()
                .and_then(|pointer| read_pointer(&dir, pointer, package, "", &mut view.notes)),
        };
        let alike = |notes: &mut Vec<String>, (token, base): &(String, PackageObligations)| {
            let alike = base.lane == now.lane
                && base.policy == now.policy
                && base.selection == now.selection;
            if !alike {
                notes.push(format!(
                    "snapshot {token} was measured on lane `{}` (policy `{}`, selection `{}`), \
                     this run on lane `{}` (policy `{}`, selection `{}`); no base",
                    base.lane, base.policy, base.selection, now.lane, now.policy, now.selection
                ));
            }
            alike
        };
        let base = base.filter(|base| alike(&mut view.notes, base));
        // The obligations' base is the last snapshot that concluded: a record
        // that did not measured no obligation. When the base did not
        // conclude, it is the caller's last concluded snapshot; `--since`
        // naming one that did not conclude has none.
        let measured = match &base {
            Some((token, record)) if record.concluded => Some((token.clone(), record.clone())),
            Some((token, _)) if since.as_ref().is_some_and(|(since, _)| since == token) => {
                view.notes.push(format!(
                    "snapshot {token} of `{package}` did not conclude; its obligations have no \
                     base"
                ));
                None
            }
            Some(_) => concluded_pointer
                .as_ref()
                .and_then(|pointer| {
                    read_pointer(&dir, pointer, package, "concluded ", &mut view.notes)
                })
                .filter(|measured| measured.1.concluded)
                .filter(|measured| alike(&mut view.notes, measured)),
            None => None,
        };
        // Stored after the base is read, so storing (and the pruning it does)
        // can never remove the base this run compares with.
        let token = match store(&dir, bytes.as_bytes()) {
            Ok(token) => Some(token),
            Err(error) => {
                view.notes.push(format!(
                    "the snapshot of `{package}` was not stored under {}: {error}",
                    dir.display()
                ));
                None
            }
        };
        let concluded = now.concluded;
        if let (Some(pointer), Some(token)) = (&pointer, &token) {
            // The pointer names this run; the concluded pointer, the last run
            // that concluded.
            let concluded_pointer = concluded_pointer.as_ref().filter(|_| concluded);
            for pointer in std::iter::once(pointer).chain(concluded_pointer) {
                let written =
                    pointer.parent().map_or(Ok(()), std::fs::create_dir_all).and_then(|()| {
                        crate::durable_io::atomic_write_private(
                            pointer,
                            format!("{token}\n").as_bytes(),
                        )
                    });
                if let Err(error) = written {
                    view.notes
                        .push(format!("your pointer to snapshot {token} was not stored: {error}"));
                }
            }
        }
        view.packages.push(PackageDelta {
            package: package.clone(),
            total: now.obligations.len(),
            compile_errors: now.compile_errors.len(),
            concluded,
            now: token,
            errors: error_rows(base.as_ref().map(|(_, base)| base), &now),
            // With no listing of the command's own, the view keeps every row
            // that is not plainly proved in sight as a `STILL` row; with one,
            // the listing keeps those rows (`crate::report`). A run that did
            // not conclude measured no obligation: its header facts are
            // compared, its obligations are not.
            since: measured
                .map(|(token, measured)| (token, changes(&measured, &now, list_rows, concluded))),
            all: if list_rows && request.all_rows {
                now.obligations.iter().map(|record| row("", record, None, false)).collect()
            } else {
                Vec::new()
            },
        });
    }
    view
}

/// [`publish`] for a crate-mode run: the record of every package the run
/// selected (every package it recorded when it names no selection), the same
/// bytes `ObligationRecords::write_records` just wrote. The check prints its
/// own listing, so the view lists no rows of its own and no `STILL` rows: the
/// listing keeps every row that is not plainly proved (`crate::report`).
pub(crate) fn publish_run(
    target_dir: &Path,
    records: &crate::obligations::ObligationRecords,
    request: &DeltaRequest,
    caller: Option<&str>,
) -> DeltaView {
    let selected = &records.scope.selected;
    // A package that reported a compile error is in the view whether or not
    // the run selected it: a dependency that did not compile is why the
    // selected packages were not verified.
    let packages: Vec<(String, String)> = records
        .units
        .keys()
        .filter(|package| {
            selected.is_empty()
                || selected.contains(*package)
                || records.compile_errors.contains_key(*package)
        })
        .filter_map(|package| records.package_ndjson(package).map(|bytes| (package.clone(), bytes)))
        .collect();
    publish(target_dir, &packages, request, caller, false)
}

/// One package's functions, by def path, from a read-back record.
fn functions_of(record: &PackageObligations) -> PackageRecords {
    let mut functions: PackageRecords = record
        .functions
        .iter()
        .map(|(path, source)| {
            (path.clone(), FunctionRecords { source: source.clone(), obligations: BTreeMap::new() })
        })
        .collect();
    for obligation in &record.obligations {
        let Some((def_path, id)) = split_obligation_key(&obligation.key) else {
            continue;
        };
        functions
            .entry(def_path.to_string())
            .or_default()
            .obligations
            .insert(id.to_string(), obligation.clone());
    }
    functions
}

fn source16(source: Option<&str>) -> Option<String> {
    source.and_then(|digest| digest.get(..16)).map(str::to_string)
}

/// The row words, in the order rows are printed.
const ORDER: [&str; 11] = [
    "RUN",
    "LOST",
    "NEW FAILED",
    "NOT MEASURED",
    "CHANGED",
    "STILL",
    "GAINED",
    "NEW",
    "VANISHED",
    "MOVED",
    "REMOVED",
];

/// The compiler-error rows of `now` against `base` (the caller's previous
/// snapshot, concluded or not): `NEW ERROR` for one the base did not have,
/// `STILL` for one it had, `CLEARED` for one of the base's no longer reported;
/// with no base, each of `now`'s errors with no word. No listing prints a
/// compile error, so every error still reported prints on every run. A key
/// names the file, code and message, never the line, so an error that only
/// moved is `STILL`. In key order, `CLEARED` rows last.
fn error_rows(base: Option<&PackageObligations>, now: &PackageObligations) -> Vec<String> {
    let Some(base) = base else {
        return now.compile_errors.iter().map(|error| error_row("", error)).collect();
    };
    let held: BTreeSet<&str> = base.compile_errors.iter().map(|error| error.key.as_str()).collect();
    let reported: BTreeSet<&str> =
        now.compile_errors.iter().map(|error| error.key.as_str()).collect();
    let mut lines: Vec<String> = now
        .compile_errors
        .iter()
        .map(|error| {
            error_row(if held.contains(error.key.as_str()) { "STILL" } else { "NEW ERROR" }, error)
        })
        .collect();
    lines.extend(
        base.compile_errors
            .iter()
            .filter(|error| !reported.contains(error.key.as_str()))
            .map(|error| error_row("CLEARED", error)),
    );
    lines
}

/// Read the snapshot a caller's pointer file names, with a note when it names
/// one that is gone or cannot be read. A pointer that does not hold a token
/// names no snapshot (`load` refuses it), never a path.
fn read_pointer(
    dir: &Path,
    pointer: &Path,
    package: &str,
    which: &str,
    notes: &mut Vec<String>,
) -> Option<(String, PackageObligations)> {
    let token = std::fs::read_to_string(pointer).ok()?.trim().to_string();
    match load(dir, &token) {
        Some(Ok(base)) => Some((token, base)),
        Some(Err(error)) => {
            notes.push(format!(
                "your previous {which}snapshot {token} of `{package}` cannot be read ({error}); \
                 no base"
            ));
            None
        }
        None => {
            notes.push(format!(
                "your previous {which}snapshot {token} of `{package}` was removed; no base"
            ));
            None
        }
    }
}

/// `WORD  [ERROR <code>]  <key>  <message>  <location>`: a compile-error row.
fn error_row(word: &str, error: &CompileErrorRecord) -> String {
    let word = if word.is_empty() { String::new() } else { label(word) };
    format!(
        "{word}[{}]  {}  {}  {}",
        error.label(),
        error.key,
        error.message,
        error.location_label()
    )
}

/// A row word padded to the twelve-column label, and always followed by at
/// least two spaces (`NOT MEASURED` fills all twelve).
fn label(word: &str) -> String {
    if word.len() >= 11 { format!("{word}  ") } else { format!("{word:<12}") }
}

/// A grade as `<encoding>/<discharge>[+<premise>…]`.
fn grade(record: &ObligationRecord) -> String {
    let mut out = format!("{}/{}", record.encoding, record.discharge);
    for premise in &record.premises {
        out.push('+');
        out.push_str(premise);
    }
    out
}

/// `WORD  [<label>]  <key>  <kind>  <status> (was <old>)  <stop>  <location>`,
/// where `<label>` is the listing's label for the row now and `(was …)` names
/// what changed: the status, else the stop, else the label, else the grade.
/// A `new` row (`new` true) says `(new)`; a `STILL` row and an `--all-rows`
/// row say nothing.
fn row(word: &str, record: &ObligationRecord, was: Option<&ObligationRecord>, new: bool) -> String {
    let was = match was {
        Some(old) if old.status != record.status => format!(" (was {})", old.status),
        Some(old) if old.stop != record.stop => format!(" (was stopped by {})", old.stop),
        Some(old) if old.listing_label() != record.listing_label() => {
            format!(" (was [{}])", old.listing_label())
        }
        Some(old) if grade(old) != grade(record) => {
            format!(" (graded {}, was {})", grade(record), grade(old))
        }
        Some(_) => String::new(),
        None if new => " (new)".to_string(),
        None => String::new(),
    };
    let word = if word.is_empty() { String::new() } else { label(word) };
    format!(
        "{word}[{}]  {}  {}  {}{was}  {}  {}",
        record.listing_label(),
        record.key,
        record.kind,
        record.status,
        record.stop,
        record.location_label()
    )
}

/// What changed between two records.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Changes {
    /// The lines to print, in [`ORDER`]; within one row word, in the order of
    /// the lines' own text (a row's listing label comes before its key).
    pub(crate) lines: Vec<String>,
    /// How many obligation rows changed (a `RUN` or `STILL` line is not one).
    pub(crate) rows: usize,
}

/// The rows that changed between `base` and `now` (module docs), and, with
/// `still`, a `STILL` row for every row unchanged but not plainly proved.
pub(crate) fn changed_rows(
    base: &PackageObligations,
    now: &PackageObligations,
    still: bool,
) -> Changes {
    changes(base, now, still, true)
}

/// [`changed_rows`], or, with `compare_obligations` false (`now` did not
/// conclude), only the header facts that moved and, with `still`, every row of
/// `now` not plainly proved as a `STILL` row.
fn changes(
    base: &PackageObligations,
    now: &PackageObligations,
    still: bool,
    compare_obligations: bool,
) -> Changes {
    // (order, line); `RUN` and `STILL` lines are not changed obligation rows.
    let mut rows: Vec<(usize, String)> = Vec::new();
    let mut changed = 0;
    let mut push = |word: &str, line: String| {
        let order = ORDER.iter().position(|w| *w == word).expect("a row word");
        changed += usize::from(word != "RUN" && word != "STILL");
        rows.push((order, line));
    };
    for (field, old, new) in [
        ("outcome", base.outcome.as_str(), now.outcome.as_str()),
        ("targo_trust_commit", base.targo_trust_commit.as_str(), now.targo_trust_commit.as_str()),
        ("profile", base.profile.as_str(), now.profile.as_str()),
    ] {
        if old != new {
            push("RUN", format!("{:<12}{field} {old} -> {new}", "RUN"));
        }
    }
    if base.coverage_complete != now.coverage_complete {
        push(
            "RUN",
            format!(
                "{:<12}coverage_complete {} -> {}",
                "RUN", base.coverage_complete, now.coverage_complete
            ),
        );
    }
    if !compare_obligations {
        // A run that did not conclude measured no obligation: none is compared,
        // and, with `still`, every row it has that is not plainly proved
        // prints, as it does on every run.
        for after in now.obligations.iter().filter(|after| still && !after.is_plainly_proved()) {
            push("STILL", row("STILL", after, None, false));
        }
        rows.sort();
        return Changes { lines: rows.into_iter().map(|(_, line)| line).collect(), rows: 0 };
    }
    let old_functions = functions_of(base);
    let new_functions = functions_of(now);
    // Pair functions as the baseline does (source digest, def path, then ids).
    let held: BTreeMap<String, BaselineFunction> = old_functions
        .iter()
        .map(|(path, function)| {
            (
                path.clone(),
                BaselineFunction {
                    source: source16(function.source.as_deref()),
                    proved: function
                        .obligations
                        .iter()
                        .filter(|(_, record)| record.is_proved())
                        .map(|(id, _)| id.clone())
                        .collect(),
                },
            )
        })
        .collect();
    let paired = pair_functions(&held, &new_functions);
    let mut claimed: BTreeSet<&str> = BTreeSet::new();
    for (old_path, old) in &old_functions {
        let Some(&(new_path, how)) = paired.get(old_path.as_str()) else {
            push(
                "REMOVED",
                format!("{:<12}{old_path}  ({} obligation(s))", "REMOVED", old.obligations.len()),
            );
            continue;
        };
        claimed.insert(new_path);
        let new = &new_functions[new_path];
        if new_path != old_path {
            push(
                "MOVED",
                format!("{:<12}{old_path} -> {new_path}  (paired by {})", "MOVED", how.as_str()),
            );
        }
        let source_changed = match (&old.source, &new.source) {
            (Some(before), Some(after)) => before != after,
            _ => false,
        };
        for (id, before) in &old.obligations {
            match new.obligations.get(id) {
                Some(after) => match compare_key(before, after) {
                    Some(word) => push(word, row(word, after, Some(before), false)),
                    None if still && !after.is_plainly_proved() => {
                        push("STILL", row("STILL", after, None, false))
                    }
                    None => {}
                },
                None if before.is_proved() && !source_changed => push(
                    "LOST",
                    format!(
                        "{:<12}{}  {}  vanished (was proved; its function's source did not \
                         change)  -  {}",
                        "LOST",
                        before.key,
                        before.kind,
                        before.location_label()
                    ),
                ),
                None => push(
                    "VANISHED",
                    format!(
                        "{:<12}{}  {}  (was {})  {}",
                        "VANISHED",
                        before.key,
                        before.kind,
                        before.status,
                        before.location_label()
                    ),
                ),
            }
        }
        for (id, after) in &new.obligations {
            if !old.obligations.contains_key(id) {
                let word = new_key(after);
                push(word, row(word, after, None, true));
            }
        }
    }
    for (new_path, new) in &new_functions {
        if claimed.contains(new_path.as_str()) {
            continue;
        }
        for after in new.obligations.values() {
            let word = new_key(after);
            push(word, row(word, after, None, true));
        }
    }
    rows.sort();
    Changes { lines: rows.into_iter().map(|(_, line)| line).collect(), rows: changed }
}

/// The word of a key present on both sides, or `None` when nothing the record
/// states about it changed but its location. Same status and stop with
/// another grade, basis or label is `CHANGED`: a proof that now rests on a new
/// premise is not the proof the base had.
fn compare_key(before: &ObligationRecord, after: &ObligationRecord) -> Option<&'static str> {
    if before.status == after.status && before.stop == after.stop {
        let same = before.encoding == after.encoding
            && before.discharge == after.discharge
            && before.premises == after.premises
            && before.basis == after.basis
            && before.listing_label() == after.listing_label();
        return (!same).then_some("CHANGED");
    }
    Some(if before.is_proved() && !after.is_proved() {
        if after.stop_is_reproducible() { "LOST" } else { "NOT MEASURED" }
    } else if after.is_proved() {
        "GAINED"
    } else if after.is_failed() && !before.is_failed() {
        "NEW FAILED"
    } else {
        "CHANGED"
    })
}

/// The word of a key present only now.
fn new_key(after: &ObligationRecord) -> &'static str {
    if after.is_proved() {
        "GAINED"
    } else if after.is_failed() {
        "NEW FAILED"
    } else {
        "NEW"
    }
}

/// `targo trust delta [--since <token>] [--all-rows] [--target-dir <dir>]
/// <record.ndjson>…`: snapshot `trust.obligations.v1` records a check already
/// wrote and print what changed since the base, exactly as the check prints
/// it, without re-running the check. Exit 0, or 2 for a usage error or a
/// record that cannot be read.
pub(crate) fn run_subcommand(args: &[String]) -> std::process::ExitCode {
    use std::process::ExitCode;
    let mut args = args.to_vec();
    let request = match DeltaRequest::take_from(&mut args) {
        Ok(request) => request,
        Err(error) => {
            eprintln!("targo trust delta: {error}");
            return ExitCode::from(2);
        }
    };
    let mut target_dir: Option<PathBuf> = None;
    let mut paths: Vec<PathBuf> = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let arg = args[index].as_str();
        if arg == "--target-dir" {
            index += 1;
            match args.get(index) {
                Some(dir) if !dir.is_empty() => target_dir = Some(PathBuf::from(dir)),
                _ => {
                    eprintln!("targo trust delta: --target-dir requires a directory");
                    return ExitCode::from(2);
                }
            }
        } else if let Some(dir) = arg.strip_prefix("--target-dir=") {
            target_dir = Some(PathBuf::from(dir));
        } else if arg == "--help" || arg == "-h" {
            println!(
                "usage: targo trust delta [--since <token>] [--all-rows] [--target-dir <dir>] \
                 <record.ndjson>...\n\
                 Snapshot the `trust.obligations.v1` records a check wrote \
                 (<target-dir>/trust/obligations/<package>.ndjson) and print the rows that \
                 changed since <token>, or since the last token this agent session was given."
            );
            return ExitCode::SUCCESS;
        } else if arg.starts_with('-') {
            eprintln!("targo trust delta: unknown option `{arg}`");
            return ExitCode::from(2);
        } else {
            paths.push(PathBuf::from(arg));
        }
        index += 1;
    }
    if paths.is_empty() {
        eprintln!("targo trust delta: name at least one `trust.obligations.v1` record");
        return ExitCode::from(2);
    }
    let mut records = Vec::new();
    for path in &paths {
        let text = match crate::input_limits::read_bounded_utf8_file(
            path,
            crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES,
        ) {
            Ok(text) => text,
            Err(error) => {
                eprintln!("targo trust delta: cannot read `{}`: {error}", path.display());
                return ExitCode::from(2);
            }
        };
        match parse_package_ndjson(&text) {
            Ok(record) => records.push((record.package, text)),
            Err(error) => {
                eprintln!("targo trust delta: `{}`: {error}", path.display());
                return ExitCode::from(2);
            }
        }
    }
    let target_dir =
        target_dir.unwrap_or_else(|| crate::pipeline::run::cargo_target_dir(&[], None));
    let caller = caller_session_from_env();
    for line in publish(&target_dir, &records, &request, caller.as_deref(), true).lines() {
        println!("{line}");
    }
    ExitCode::SUCCESS
}

#[cfg(test)]
#[path = "agent_delta_tests.rs"]
mod tests;
