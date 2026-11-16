// targo-trust/agent_delta.rs: changed-only results for the editing agent
// (live-edit-loop plan, step 2 DELTA; docs/design/2026-11-12-live-edit-loop.md).
// What a user sees is in docs/cli-reference.md, under `targo trust delta`.
//
// A run's view covers `trust.obligations.v1` records (`crate::obligations`),
// one per package: a crate-mode check's or test run's selected packages and
// any package that reported a compiler error ([`publish_run`]), a `.lean`
// check's files, or the records `targo trust delta` is given. Each is kept as
// a SNAPSHOT under `<target-dir>/trust/snapshots/<token>` (with no target
// directory, nowhere: [`unstored`]), the token being the first sixteen hex
// digits of the SHA-256 of the whole record, so equal tokens are equal
// records.
//
// Each package is compared with a BASE snapshot ([`publish`]): with
// `--since <token>`, that snapshot, for its own package only (the others have
// none, and no pointer stands in for a snapshot `--since` names that cannot be
// read); without it, the one its CALLER's pointer names ([`read_pointer`]).
// The caller is the session the environment names ([`caller_session_from_env`]),
// not an agent: agents that share one session's environment and one target
// directory share its pointers. The pointers live under the snapshot
// directory, per package, lane, policy and selection, and for a test run its
// libtest arguments too ([`pointer_path`]): one for the last run, a second
// for the last run that concluded and a third for the last run that measured
// its islands (below). Every base of a run is read before any snapshot is
// stored, so the pruning a store does removes no base the run compares with,
// and each pointer moves to a token only once the view naming it was printed
// ([`DeltaView::commit_pointers`]). A base measured on another lane, policy
// or selection, or by a run of the other kind (a check's for a test run) or
// given other libtest arguments, is not used.
//
// The view prints the rows that changed ([`changed_rows`]) and one summary
// line per package ([`PackageDelta::summary_line`]). It hides no row the
// listing does not label a plain `PROVED`: a crate-mode check's report keeps it
// (`crate::report`, [`DeltaView::replaces_listing`]); where the command prints
// no per-row listing, the view lists it ([`listed_rows`], [`changed_rows`]).
//
// Compiler errors are rows too. A package with an error-level compiler
// diagnostic (a compile error, or the verifier's own refusal) carries one
// error line per error in its record (`crate::obligations`), keyed by file,
// error code and normalized message, never by line, so an edit elsewhere in
// the file keeps the key. They are compared with the package's base, whatever
// it measured ([`error_rows`]): a new one is `NEW ERROR`, one no longer
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
// reported an error is in a crate-mode check's view whether or not the run
// selected it (a dependency that did not compile; [`publish_run`]). The
// verdict, the gate lines and the exit status are the run's own: a package
// that did not compile is `could-not-run`.
//
// Test results are rows too. A `targo trust test` run's record carries one row
// per test harness and one per case (`crate::obligations`, TEST RESULTS;
// `crate::test_results`), compared with the caller's previous snapshot of a
// test run given the same libtest arguments (a test run's pointer is its own:
// its header names those arguments in `"tests"`, so it is never compared with
// a check, nor with a run that a filter or `--ignored` gave other cases). A
// case that failed or did not conclude, and a harness that did not conclude,
// prints on every run (`STILL` once unchanged), as a failing obligation does;
// a case newly failed is `NEW FAILED`; a passed or ignored case prints only
// when it changed (`CHANGED`, `NEW`, or `VANISHED` when its harness concluded
// without it); a case the base had failed that a harness which did not
// conclude no longer reports is `STILL` not concluded `(was failed)`; a
// harness gone is `REMOVED`. With no base, the rows that are not passed or
// ignored print. Every test row but a `REMOVED` harness line (`REMOVED
// <harness>  (N test case(s))`) says `reported by its harness` and the
// summary line says the outcomes are what each test binary's own harness
// reported: the harness is linked into the user's program, so a test row is
// never proof, prints no proof word and moves no verdict. The summary line
// gains `; K of T test case(s) changed: …` (or `; T test case(s): …` with no
// base), where K counts the case rows that are new, changed or vanished: a
// harness row is not a case and is not counted ([`test_rows`]).
//
// Island declarations are rows too. A crate's `clean { … }` islands carry one
// row per declaration in the record's island section (`crate::obligations`,
// CLEAN ISLANDS), keyed as a `.lean` declaration is, so a proof edit keeps the
// key and a statement edit is a new key. No listing prints them, so every
// island row not plainly proved prints on every run (`STILL`). They are
// compared with the caller's last snapshot that MEASURED its islands — every
// proof unit of the package published its island rows (its units are WHOLE)
// and every section is `verified` and complete — through a third pointer,
// `<pointer>.islands`, which only such a run moves, independently of the
// obligations' `concluded` base (`--since` names the islands' base too, and a
// snapshot it names that did not measure them gives them none;
// [`island_rows`]):
//
// * a base row missing now is `VANISHED` only where the package's units are
//   whole and now's section of its crate, if any, is complete. Otherwise it
//   is not a deleted claim: where a unit published nothing (a Rust parse
//   error stopped it before its islands were read), a base row that was not
//   failed is counted in one `NOT MEASURED` line per crate naming why, and a
//   failed one prints on its own; where an island did not parse, each is
//   `NOT MEASURED`;
// * in a section that is not a measurement — a Rust front-end error stopped
//   the crate (`front-end-error`: the resolver's batch, with no model,
//   binding or seal check), a unit of the package published nothing, or the
//   rows are incomplete (a tainted session, an island that did not parse) —
//   only the refused rows and new keys are compared (`NEW FAILED`, `STILL`,
//   `NEW`), a row the base had failed that is not now is `CHANGED`, and every
//   other row is one `NOT CHECKED` line naming how many and why, so a Rust
//   typo far from any island, or one session taint, does not print every
//   island row; `--all-rows` lists them.
//
// The summary line gains `; K of D island declaration(s) changed` (`; D island
// declaration(s)` with no base; `since <token>` after it when the islands'
// base is not the obligations' base), where D is this run's island rows and
// K counts every island line except a `STILL` row and the `NOT CHECKED` and
// `NOT MEASURED` count lines: the rows that changed, each `VANISHED` row and
// each single `NOT MEASURED` row. The last two are base rows with no row now,
// so they are not among D and K can exceed it; K is never added to `N`;
// `; islands not measured: <why>` when a unit published nothing (`; islands
// not measured this run: <why>` in place of the count when no unit did); and `; islands incomplete: <crate>: <problem>; …` when a
// section is not complete. A package that has no island section and whose
// base has none prints exactly what it printed before islands had rows.
//
// Snapshots and pointers are observational: a write failure is a note, never
// a verdict or an exit status, and no verdict is read from a snapshot. A
// snapshot whose bytes do not hash to its name is refused ([`load`]).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use sha2::{Digest, Sha256};
use trust_types::obligation_identity::split_obligation_key;

use crate::baseline::{BaselineFunction, pair_functions};
use crate::obligations::clean_islands::{CleanDeclRecord, CleanIslandSection, PackageCleanIslands};
use crate::obligations::{
    CompileErrorRecord, FunctionRecords, ObligationRecord, PackageObligations, PackageRecords,
    parse_package_ndjson,
};

/// The environment variables that name the calling agent session, in order.
/// Every one that is set and not empty joins the caller's identity.
pub(crate) const CALLER_SESSION_ENV: [&str; 2] = ["ATERM_SESSION_ID", "CLAUDE_CODE_SESSION_ID"];

/// How long a snapshot nobody read or wrote is kept.
pub(crate) const SNAPSHOT_RETENTION: Duration = Duration::from_secs(7 * 24 * 60 * 60);

/// How long a caller pointer nobody wrote is kept: longer than a snapshot, so
/// that a pointer whose snapshot was pruned says so (`read_pointer`) rather
/// than leaving its caller a silent first run.
pub(crate) const POINTER_RETENTION: Duration = Duration::from_secs(30 * 24 * 60 * 60);

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
    let mut measurement =
        format!("{}\0{}\0{}\0{}", record.package, record.lane, record.policy, record.selection);
    // A test run compiles test units and runs them: never a check's base.
    // Its harnesses' arguments choose which cases run: a run given other
    // arguments (a filter, `--ignored`) is never its base either.
    if let Some(arguments) = &record.tests {
        measurement.push_str("\0tests\0");
        measurement.push_str(&serde_json::Value::from(arguments.clone()).to_string());
    }
    dir.join("callers").join(sha16(caller.as_bytes())).join(sha16(measurement.as_bytes()))
}

/// Mark `path` as used now, so retention counts from this read.
fn touch(path: &Path) {
    if let Ok(file) = std::fs::OpenOptions::new().write(true).open(path) {
        let _ = file.set_modified(SystemTime::now());
    }
}

/// Whether `path` was last modified (written, or marked used by [`touch`])
/// more than `retention` before `now`.
fn older_than(path: &Path, retention: Duration, now: SystemTime) -> bool {
    std::fs::metadata(path)
        .and_then(|meta| meta.modified())
        .is_ok_and(|modified| now.duration_since(modified).unwrap_or_default() > retention)
}

/// Remove every snapshot under `dir` last used more than
/// [`SNAPSHOT_RETENTION`] ago, except `keep`, and every caller pointer last
/// written more than [`POINTER_RETENTION`] ago. Returns how many were removed.
fn prune(dir: &Path, keep: &Path, now: SystemTime) -> usize {
    let stale = |path: &Path, retention: Duration| path != keep && older_than(path, retention, now);
    let mut removed = 0;
    let Ok(entries) = std::fs::read_dir(dir) else {
        return 0;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().into_owned();
        if is_token(&name) && path.is_file() && stale(&path, SNAPSHOT_RETENTION) {
            removed += usize::from(std::fs::remove_file(&path).is_ok());
        }
    }
    let callers = dir.join("callers");
    for caller in std::fs::read_dir(&callers).into_iter().flatten().flatten() {
        let caller = caller.path();
        for pointer in std::fs::read_dir(&caller).into_iter().flatten().flatten() {
            let pointer = pointer.path();
            if pointer.is_file() && stale(&pointer, POINTER_RETENTION) {
                removed += usize::from(std::fs::remove_file(&pointer).is_ok());
            }
        }
        let _ = std::fs::remove_dir(&caller);
    }
    removed
}

/// Store `bytes` as a snapshot and return its token. An existing snapshot of
/// the same token whose bytes hash to it is the same record and is only marked
/// used; any other is (re)written, and once it is written the stale ones (never
/// it) are removed.
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
    /// Where the command prints no listing of its own (a `.lean` check,
    /// `targo trust delta`): every obligation row of this run with
    /// `--all-rows`, else, with no obligation base, every one that is not
    /// plainly proved ([`listed_rows`]).
    pub(crate) all: Vec<String>,
    /// A test run's test rows (`test_rows`): no listing prints them.
    pub(crate) tests: Vec<String>,
    /// A test run's case counts, for its summary line.
    pub(crate) test_summary: Option<TestSummary>,
    /// The island declaration rows (`island_rows`): no listing prints them.
    pub(crate) islands: Vec<String>,
    /// The island counts, for the summary line; `None` when neither this
    /// run nor its island base has an island section.
    pub(crate) island_summary: Option<IslandSummary>,
}

/// A package's island declarations, for its summary line.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct IslandSummary {
    /// The island declaration rows of this run.
    pub(crate) total: usize,
    /// How many island lines count as changed since the island base (every
    /// line but `STILL` rows and the two count lines; `VANISHED` and single
    /// `NOT MEASURED` rows included); `None` with no base.
    pub(crate) changed: Option<usize>,
    /// The islands' base token, when there is one.
    pub(crate) base: Option<String>,
    /// Every section's problems, `<crate>: <problem>`, when one is not
    /// complete.
    pub(crate) problems: Vec<String>,
    /// Why the package's units are not whole: a unit published no island
    /// rows, so a key missing now is not a deleted claim.
    pub(crate) not_measured: Option<String>,
    /// Whether this run has an island section at all.
    pub(crate) any_section: bool,
}

impl IslandSummary {
    /// `; K of D island declaration(s) changed[ since <base>]` (`; D island
    /// declaration(s)` with no base; `since` only when the islands' base is
    /// not `obligations_base`), then `; islands not measured: <why>` when a
    /// unit published nothing, then `; islands incomplete: …` when a section
    /// is not complete; or, with no section at all and a unit that published
    /// nothing, `; islands not measured this run: <why>` in place of the
    /// count.
    fn clause(&self, obligations_base: Option<&str>) -> String {
        let mut clause = match (&self.not_measured, self.any_section) {
            (Some(why), false) => format!("; islands not measured this run: {why}"),
            _ => {
                let mut lead = match self.changed {
                    Some(changed) => {
                        format!("; {changed} of {} island declaration(s) changed", self.total)
                    }
                    None => format!("; {} island declaration(s)", self.total),
                };
                if let Some(base) =
                    self.base.as_deref().filter(|base| obligations_base != Some(*base))
                {
                    lead.push_str(&format!(" since {base}"));
                }
                if let Some(why) = &self.not_measured {
                    lead.push_str(&format!("; islands not measured: {why}"));
                }
                lead
            }
        };
        if !self.problems.is_empty() {
            clause.push_str("; islands incomplete: ");
            clause.push_str(&self.problems.join("; "));
        }
        clause
    }
}

/// A test run's cases by outcome, and how many test rows changed since the
/// base (`None` with no base).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct TestSummary {
    pub(crate) passed: usize,
    pub(crate) failed: usize,
    pub(crate) ignored: usize,
    pub(crate) not_concluded: usize,
    pub(crate) harnesses_not_concluded: usize,
    pub(crate) changed: Option<usize>,
}

impl TestSummary {
    fn of(record: &PackageObligations, changed: Option<usize>) -> Self {
        use crate::test_results::CaseOutcome;
        let count = |outcome: CaseOutcome| {
            record.test_cases.iter().filter(|case| case.outcome == outcome).count()
        };
        Self {
            passed: count(CaseOutcome::Passed),
            failed: count(CaseOutcome::Failed),
            ignored: count(CaseOutcome::Ignored),
            not_concluded: count(CaseOutcome::NotConcluded),
            harnesses_not_concluded: record
                .test_harnesses
                .iter()
                .filter(|harness| !harness.concluded)
                .count(),
            changed,
        }
    }

    /// `; K of T test case(s) changed: P passed, F failed, I ignored, U not
    /// concluded[, H harness(es) not concluded] (reported by each test
    /// binary's own harness)`, or `; T test case(s): …` with no base. K
    /// counts case rows only (`test_rows`), never a harness row.
    fn clause(&self) -> String {
        let total = self.passed + self.failed + self.ignored + self.not_concluded;
        let lead = match self.changed {
            Some(changed) => format!("{changed} of {total} test case(s) changed"),
            None => format!("{total} test case(s)"),
        };
        let harnesses = if self.harnesses_not_concluded > 0 {
            format!(", {} harness(es) not concluded", self.harnesses_not_concluded)
        } else {
            String::new()
        };
        format!(
            "; {lead}: {} passed, {} failed, {} ignored, {} not concluded{harnesses} (reported \
             by each test binary's own harness)",
            self.passed, self.failed, self.ignored, self.not_concluded
        )
    }
}

impl PackageDelta {
    /// `<package>  N of M changed since <old>  (now <new>)`, where `M` is
    /// this run's rows and the base's rows that have none now, or, with no
    /// base, `<package>  M obligation(s)  (now <new>)`; a package that reported
    /// compiler errors leads with `K compiler error(s); `, and one that
    /// reported none but whose record did not conclude (a dependency did not
    /// compile) with `not concluded; `. A record that did not conclude and
    /// has a base says so in place of a changed count it did not measure:
    /// `<package>  K compiler error(s); obligations not compared since <old>
    /// (now <new>)`. With no base it keeps `M obligation(s)`, the rows its
    /// record holds. A test run's and the islands' clauses
    /// ([`TestSummary::clause`], [`IslandSummary::clause`]) go before
    /// `(now <new>)`.
    pub(crate) fn summary_line(&self) -> String {
        let line = self.obligation_summary();
        let obligations_base = self.since.as_ref().map(|(token, _)| token.as_str());
        let clauses: String = self
            .test_summary
            .iter()
            .map(TestSummary::clause)
            .chain(self.island_summary.iter().map(|islands| islands.clause(obligations_base)))
            .collect();
        if clauses.is_empty() {
            return line;
        }
        match line.rfind("  (now ") {
            Some(at) => format!("{}{clauses}{}", &line[..at], &line[at..]),
            None => format!("{line}{clauses}"),
        }
    }

    fn obligation_summary(&self) -> String {
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
                changes.rows,
                self.total + changes.gone
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
    /// The caller pointers this view moves once it was printed
    /// ([`Self::commit_pointers`]): each pointer file and the token it is to
    /// name, which this view's summary line prints.
    pointers: Vec<(PathBuf, String)>,
}

impl DeltaView {
    /// Move each caller pointer to the token this view prints for its
    /// package. Call it only once the view was printed, so a caller's base is
    /// always a token it was shown: a run whose view is never printed (its
    /// report not printed, say) leaves the base where it was. Returns a note
    /// for each pointer not stored, to print after the view.
    pub(crate) fn commit_pointers(&self) -> Vec<String> {
        let mut notes = Vec::new();
        for (pointer, token) in &self.pointers {
            let written = pointer.parent().map_or(Ok(()), std::fs::create_dir_all).and_then(|()| {
                crate::durable_io::atomic_write_private(pointer, format!("{token}\n").as_bytes())
            });
            if let Err(error) = written {
                notes.push(format!("your pointer to snapshot {token} was not stored: {error}"));
            }
        }
        notes
    }

    /// Whether the command's own listing is narrowed to its rows that are not
    /// plainly proved, followed by the view (`crate::report`,
    /// `terminal_lines_with`): the view covers at least one package, every one
    /// had a base, and `--all-rows` was not given. Otherwise the whole listing
    /// prints, then the view. A run that fails the evidence gate prints the
    /// whole listing whatever this says (`crate::report`).
    pub(crate) fn replaces_listing(&self) -> bool {
        !self.all_rows
            && !self.packages.is_empty()
            && self.packages.iter().all(|package| package.since.is_some())
    }

    /// The lines to print: the notes, then per package its compile-error
    /// rows, test rows, island rows, the rows of [`PackageDelta::all`], its
    /// changed obligation rows and its summary line.
    pub(crate) fn lines(&self) -> Vec<String> {
        let mut lines: Vec<String> =
            self.notes.iter().map(|note| format!("note: {note}")).collect();
        for package in &self.packages {
            lines.extend(package.errors.iter().cloned());
            lines.extend(package.tests.iter().cloned());
            lines.extend(package.islands.iter().cloned());
            lines.extend(package.all.iter().cloned());
            if let Some((_, changes)) = &package.since {
                lines.extend(changes.lines.iter().cloned());
            }
            lines.push(package.summary_line());
        }
        lines
    }
}

/// Snapshot each `(package, record bytes)` under `target_dir` and compare it
/// with its base. The caller's pointer is not moved here: the view holds the
/// move until it was printed ([`DeltaView::commit_pointers`]).
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
                "snapshot {token} is not under {} (never stored there, or removed since; one \
                 unused for 7 days is pruned); no base",
                dir.display()
            ));
            None
        }
    });
    // With `--since`, only the snapshot's own package has a base: the caller
    // asked for that base, so no pointer stands in for it, nor for another
    // package's.
    if let Some((token, base)) = &since {
        let named = base.package.as_str();
        if !records.iter().any(|(package, _)| package == named) {
            view.notes.push(format!(
                "snapshot {token} is package `{named}`, which this run does not snapshot; no base"
            ));
        } else if records.iter().any(|(package, _)| package != named) {
            view.notes.push(format!(
                "snapshot {token} is package `{named}`; with --since, the run's other packages \
                 have no base"
            ));
        }
    }
    // Every base is read (and so marked used) before any snapshot is stored,
    // so the pruning a store does can never remove a base this run compares
    // with, whichever package's it is and whichever pointer names it.
    let mut measured = Vec::new();
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
            _ if request.since.is_some() => None,
            _ => pointer
                .as_ref()
                .and_then(|pointer| read_pointer(&dir, pointer, package, "", &mut view.notes)),
        };
        let alike = |notes: &mut Vec<String>, (token, base): &(String, PackageObligations)| {
            let alike = base.lane == now.lane
                && base.policy == now.policy
                && base.selection == now.selection
                && base.tests == now.tests;
            let kind = |record: &PackageObligations| {
                if record.tests.is_some() { "test" } else { "check" }
            };
            if alike {
                return true;
            }
            notes.push(match (&base.tests, &now.tests) {
                (Some(was), Some(is)) if was != is => format!(
                    "snapshot {token}'s test harnesses were given `{}` and this run's `{}`; \
                     no base",
                    was.join(" "),
                    is.join(" ")
                ),
                (was, is) if was.is_some() != is.is_some() => format!(
                    "snapshot {token} is a {} run's and this is a {} run's; no base",
                    kind(base),
                    kind(&now)
                ),
                _ => format!(
                    "snapshot {token} was measured on lane `{}` (policy `{}`, selection `{}`), \
                     this run on lane `{}` (policy `{}`, selection `{}`); no base",
                    base.lane, base.policy, base.selection, now.lane, now.policy, now.selection
                ),
            });
            false
        };
        let base = base.filter(|base| alike(&mut view.notes, base));
        // The obligations' base is the last snapshot that concluded: a record
        // that did not measured no obligation. When the base did not
        // conclude, it is the caller's last concluded snapshot; `--since`
        // naming one that did not conclude has none.
        let concluded = match &base {
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
        // The islands' base is the last snapshot that measured them (a third
        // pointer, `<pointer>.islands`, which only such a run moves): a run
        // whose islands a Rust front-end error stopped, or a unit of which
        // published none, compares with the last run that measured them, and
        // never becomes the base. `--since` names this base too: a snapshot
        // it names that did not measure them, or that is not alike, gives
        // them none, and so does one that is another package's or cannot be
        // read (no pointer stands in for the base the caller asked for).
        let islands_pointer = pointer.as_ref().map(|pointer| pointer.with_extension("islands"));
        let since_here = since.as_ref().is_some_and(|(_, since)| since.package == *package);
        let islands = match &base {
            Some((token, record)) if islands_measured(record) => {
                Some((token.clone(), record.clone()))
            }
            Some((token, record)) if since_here => {
                // Said only where there are islands to compare: a package
                // with none prints what it printed before islands had rows.
                if !record.clean_islands.is_empty() || !now.clean_islands.is_empty() {
                    view.notes.push(format!(
                        "snapshot {token} of `{package}` did not measure its islands; they have \
                         no base"
                    ));
                }
                None
            }
            _ if request.since.is_some() => None,
            _ => islands_pointer
                .as_ref()
                .and_then(|pointer| {
                    read_pointer(&dir, pointer, package, "islands ", &mut view.notes)
                })
                .filter(|measured| islands_measured(&measured.1))
                .filter(|measured| alike(&mut view.notes, measured)),
        };
        let pointers = pointer.map(|pointer| [Some(pointer), concluded_pointer, islands_pointer]);
        measured.push((package, bytes, now, pointers, Bases { last: base, concluded, islands }));
    }
    for (package, bytes, now, pointers, bases) in measured {
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
        if let (Some([pointer, concluded_pointer, islands_pointer]), Some(token)) =
            (pointers, &token)
        {
            // The pointer names this run; the concluded pointer, the last run
            // that concluded; the islands pointer, the last run that measured
            // its islands, once a run of this package has had one. Each moves
            // only once the view naming the token was printed.
            let concluded_pointer = concluded_pointer.filter(|_| now.concluded);
            let islands_pointer = islands_pointer.filter(|_| {
                islands_measured(&now)
                    && (!now.clean_islands.sections.is_empty()
                        || bases
                            .islands
                            .as_ref()
                            .is_some_and(|(_, base)| !base.clean_islands.sections.is_empty()))
            });
            view.pointers.extend(
                pointer
                    .into_iter()
                    .chain(concluded_pointer)
                    .chain(islands_pointer)
                    .map(|pointer| (pointer, token.clone())),
            );
        }
        view.packages.push(package_delta(package, &now, token, bases, request, list_rows));
    }
    view
}

/// [`publish`] for a view that was printed: the caller's pointers move, as
/// they do once a command printed its view. For tests that run one caller
/// more than once.
#[cfg(test)]
pub(crate) fn publish_shown(
    target_dir: &Path,
    records: &[(String, String)],
    request: &DeltaRequest,
    caller: Option<&str>,
    list_rows: bool,
) -> DeltaView {
    let view = publish(target_dir, records, request, caller, list_rows);
    assert_eq!(view.commit_pointers(), Vec::<String>::new(), "{view:?}");
    view
}

/// The snapshots one package's record is compared with, each with its token.
#[derive(Default)]
struct Bases {
    /// The package's base, whatever it measured: its compile-error rows and
    /// test rows are compared with it.
    last: Option<(String, PackageObligations)>,
    /// The obligations' base: the last snapshot that concluded.
    concluded: Option<(String, PackageObligations)>,
    /// The islands' base: the last snapshot that measured them.
    islands: Option<(String, PackageObligations)>,
}

/// One package's place in a view: the record `now`, stored as `token` (or not
/// stored), against its `bases`. `list_rows` says the command prints no
/// listing of its own, so the view keeps every obligation row that is not
/// plainly proved in sight ([`listed_rows`], or a changed or `STILL` row);
/// otherwise the command's own report keeps them (`crate::report`).
fn package_delta(
    package: &str,
    now: &PackageObligations,
    token: Option<String>,
    bases: Bases,
    request: &DeltaRequest,
    list_rows: bool,
) -> PackageDelta {
    let concluded = now.concluded;
    let last = bases.last.as_ref().map(|(_, base)| base);
    let (tests, test_summary) = if now.tests.is_some() {
        let (rows, changed) = test_rows(last, now, request.all_rows);
        (rows, Some(TestSummary::of(now, changed)))
    } else {
        (Vec::new(), None)
    };
    let (islands, island_summary) =
        match island_rows(bases.islands.as_ref().map(|(_, base)| base), now, request.all_rows) {
            Some((rows, summary)) => (
                rows,
                Some(IslandSummary {
                    base: bases.islands.as_ref().map(|(token, _)| token.clone()),
                    ..summary
                }),
            ),
            None => (Vec::new(), None),
        };
    let all = if list_rows {
        listed_rows(now, request.all_rows, bases.concluded.is_some())
    } else {
        Vec::new()
    };
    PackageDelta {
        tests,
        test_summary,
        islands,
        island_summary,
        package: package.to_string(),
        total: now.obligations.len(),
        compile_errors: now.compile_errors.len(),
        concluded,
        now: token,
        errors: error_rows(last, now),
        // A run that did not conclude measured no obligation: its header
        // facts are compared, its obligations are not. With `--all-rows`,
        // `all` holds every row, so no `STILL` row repeats one.
        since: bases.concluded.map(|(token, base)| {
            (token, changes(&base, now, list_rows && !request.all_rows, concluded))
        }),
        all,
    }
}

/// The obligation rows of `now` a view lists where the command prints no
/// listing of its own: every row with `--all-rows`, else, with no obligation
/// base, every row that is not plainly proved (with a base, those print as
/// changed or `STILL` rows).
fn listed_rows(now: &PackageObligations, all_rows: bool, has_base: bool) -> Vec<String> {
    if all_rows {
        now.obligations.iter().map(|record| row("", record, None, false)).collect()
    } else if has_base {
        Vec::new()
    } else {
        now.obligations
            .iter()
            .filter(|record| !record.is_plainly_proved())
            .map(|record| row("", record, None, false))
            .collect()
    }
}

/// The view of records that have nowhere to be kept (a `.lean` check that can
/// name no target directory): no snapshot, no base and no pointer, so each
/// package lists the rows [`publish`] lists with no base, then its summary
/// line, `<package>  M obligation(s)  (now not stored)`.
pub(crate) fn unstored(records: &[(String, String)], request: &DeltaRequest) -> DeltaView {
    let mut view = DeltaView { all_rows: request.all_rows, ..DeltaView::default() };
    for (package, bytes) in records {
        match parse_package_ndjson(bytes) {
            Ok(now) => view.packages.push(package_delta(
                package,
                &now,
                None,
                Bases::default(),
                request,
                true,
            )),
            Err(error) => {
                view.notes.push(format!("the record of `{package}` cannot be read back: {error}"))
            }
        }
    }
    view
}

/// [`publish`] for a crate-mode run: the record of every package the run
/// selected (every package it recorded when it names no selection), the
/// bytes `ObligationRecords::write_records` writes for a check (a test run
/// writes none; its record lives only in its snapshot). The run's own report
/// keeps every obligation row that is not plainly proved (`crate::report`),
/// so the view lists no obligation rows of its own and no obligation `STILL`
/// rows; compile-error, test and island rows, which no listing prints, still
/// print as `STILL`. Its pointers move once the report printed it
/// (`crate::pipeline::run::render_report_for_run`).
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
const ORDER: [&str; 12] = [
    "RUN",
    "LOST",
    "NEW FAILED",
    "NOT MEASURED",
    "NOT CHECKED",
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

/// `WORD  [TEST <outcome>]  <key>  test  <outcome> (was …)  reported by its
/// harness  -`: a test case row.
fn case_row(
    word: &str,
    case: &crate::test_results::TestCaseRecord,
    was: Option<&crate::test_results::TestCaseRecord>,
) -> String {
    let word = if word.is_empty() { String::new() } else { label(word) };
    let outcome = case.outcome.as_str();
    let was = match was {
        Some(old) if old.outcome != case.outcome => format!(" (was {})", old.outcome.as_str()),
        _ => String::new(),
    };
    format!(
        "{word}[TEST {outcome}]  {}  test  {outcome}{was}  reported by its harness  -",
        case.key
    )
}

/// `WORD  [TEST HARNESS <state>]  <key>  harness  <state>[: <reason>] (was …)
/// reported by its harness  -`: a test harness row.
fn harness_row(
    word: &str,
    harness: &crate::test_results::TestHarnessRecord,
    was: Option<&crate::test_results::TestHarnessRecord>,
) -> String {
    let state = |harness: &crate::test_results::TestHarnessRecord| {
        if harness.concluded { "concluded" } else { "not concluded" }
    };
    let word = if word.is_empty() { String::new() } else { label(word) };
    let reason = harness.reason.as_deref().map(|reason| format!(": {reason}")).unwrap_or_default();
    let was = match was {
        Some(old) if old != harness => match &old.reason {
            Some(reason) => format!(" (was {}: {reason})", state(old)),
            None => format!(" (was {})", state(old)),
        },
        _ => String::new(),
    };
    format!(
        "{word}[TEST HARNESS {}]  {}  harness  {}{reason}{was}  reported by its harness  -",
        state(harness),
        harness.key,
        state(harness)
    )
}

/// Which kind of test row `test_rows` printed.
#[derive(Clone, Copy, PartialEq, Eq)]
enum TestRow {
    Harness,
    Case,
}

/// The test rows of a test run's record `now` against `base` (module docs),
/// with every row first under `all_rows`, and how many case rows changed
/// (`None` with no base). In [`ORDER`], then by text.
fn test_rows(
    base: Option<&PackageObligations>,
    now: &PackageObligations,
    all_rows: bool,
) -> (Vec<String>, Option<usize>) {
    use crate::test_results::CaseOutcome;
    let unsettled =
        |outcome: CaseOutcome| matches!(outcome, CaseOutcome::Failed | CaseOutcome::NotConcluded);
    let mut lines: Vec<String> = Vec::new();
    if all_rows {
        lines.extend(now.test_harnesses.iter().map(|harness| harness_row("", harness, None)));
        lines.extend(now.test_cases.iter().map(|case| case_row("", case, None)));
    }
    let Some(base) = base.filter(|base| base.tests.is_some()) else {
        if !all_rows {
            lines.extend(
                now.test_harnesses
                    .iter()
                    .filter(|harness| !harness.concluded)
                    .map(|harness| harness_row("", harness, None)),
            );
            lines.extend(
                now.test_cases
                    .iter()
                    .filter(|case| unsettled(case.outcome))
                    .map(|case| case_row("", case, None)),
            );
        }
        return (lines, None);
    };
    // `changed` counts case rows only (a case new, changed or vanished): a
    // harness row says how its harness ended, not what a case reported, so
    // the summary's `K of T test case(s) changed` never counts one.
    let mut rows: Vec<(usize, String)> = Vec::new();
    let mut changed = 0;
    let mut push = |row: TestRow, word: &str, line: String| {
        changed += usize::from(row == TestRow::Case && word != "STILL");
        rows.push((ORDER.iter().position(|w| *w == word).expect("a row word"), line));
    };
    let base_harnesses: BTreeMap<&str, &crate::test_results::TestHarnessRecord> =
        base.test_harnesses.iter().map(|harness| (harness.key.as_str(), harness)).collect();
    let now_harnesses: BTreeMap<&str, &crate::test_results::TestHarnessRecord> =
        now.test_harnesses.iter().map(|harness| (harness.key.as_str(), harness)).collect();
    for harness in &now.test_harnesses {
        match base_harnesses.get(harness.key.as_str()) {
            Some(old) if *old == harness => {
                if !harness.concluded {
                    push(TestRow::Harness, "STILL", harness_row("STILL", harness, None));
                }
            }
            Some(old) => {
                push(TestRow::Harness, "CHANGED", harness_row("CHANGED", harness, Some(old)))
            }
            None if !harness.concluded => {
                push(TestRow::Harness, "NEW", harness_row("NEW", harness, None))
            }
            None => {}
        }
    }
    for old in &base.test_harnesses {
        if !now_harnesses.contains_key(old.key.as_str()) {
            let cases = base.test_cases.iter().filter(|case| case.harness() == old.key).count();
            push(
                TestRow::Harness,
                "REMOVED",
                format!("{:<12}{}  ({cases} test case(s))", "REMOVED", old.key),
            );
        }
    }
    let base_cases: BTreeMap<&str, &crate::test_results::TestCaseRecord> =
        base.test_cases.iter().map(|case| (case.key.as_str(), case)).collect();
    let now_cases: BTreeSet<&str> = now.test_cases.iter().map(|case| case.key.as_str()).collect();
    for case in &now.test_cases {
        match base_cases.get(case.key.as_str()) {
            Some(old) if old.outcome == case.outcome => {
                if unsettled(case.outcome) {
                    push(TestRow::Case, "STILL", case_row("STILL", case, None));
                }
            }
            Some(old) => {
                let word =
                    if case.outcome == CaseOutcome::Failed { "NEW FAILED" } else { "CHANGED" };
                push(TestRow::Case, word, case_row(word, case, Some(old)));
            }
            None => {
                let word = if case.outcome == CaseOutcome::Failed { "NEW FAILED" } else { "NEW" };
                push(TestRow::Case, word, case_row(word, case, None));
            }
        }
    }
    for old in &base.test_cases {
        // A case gone from a harness that concluded is `VANISHED`; one gone
        // from a harness that did not conclude is under that harness's row,
        // except that one the base had failed is a `STILL` not-concluded row
        // `(was failed)`: a failure is never shown less than the base showed
        // it. One whose harness is gone is under its `REMOVED` row.
        if now_cases.contains(old.key.as_str()) {
            continue;
        }
        let Some(harness) = now_harnesses.get(old.harness()) else {
            continue;
        };
        if !harness.concluded {
            if old.outcome == CaseOutcome::Failed {
                let now = crate::test_results::TestCaseRecord {
                    key: old.key.clone(),
                    outcome: CaseOutcome::NotConcluded,
                };
                push(TestRow::Case, "STILL", case_row("STILL", &now, Some(old)));
            }
        } else {
            push(
                TestRow::Case,
                "VANISHED",
                format!(
                    "{:<12}{}  test  (was {})  reported by its harness  -",
                    "VANISHED",
                    old.key,
                    old.outcome.as_str()
                ),
            );
        }
    }
    rows.sort();
    lines.extend(rows.into_iter().map(|(_, line)| line));
    (lines, Some(changed))
}

/// Whether `record` measured its island declarations: every proof unit of
/// the package published its island rows and every island section is
/// `verified` and complete (`PackageCleanIslands::measured`). Only such a
/// record is an islands base.
fn islands_measured(record: &PackageObligations) -> bool {
    record.clean_islands.measured()
}

/// Why `section` of a crate in `now` (or its absence) is not a measurement of
/// that crate's island declarations, or `None` when it is: a Rust front-end
/// error stopped it, a unit of the package published no island rows, or its
/// rows are incomplete.
fn not_measured_because(
    now: &PackageCleanIslands,
    section: Option<&CleanIslandSection>,
) -> Option<String> {
    use trust_types::clean_island_rows::CleanIslandPhase;
    if section.is_some_and(|section| section.phase == CleanIslandPhase::FrontEndError) {
        return Some("a Rust front-end error stopped the crate before verification".to_string());
    }
    if let Some(why) = now.units_problem() {
        return Some(why);
    }
    section
        .is_some_and(|section| !section.complete)
        .then(|| "its island rows are incomplete".to_string())
}

/// `NOT CHECKED  <n> island declaration(s) of `<crate>` not checked: <why>
/// …`: the one line that stands for the rows of a section that is not a
/// measurement.
fn not_checked_line(crate_name: &str, count: usize, why: &str) -> String {
    format!(
        "{}{count} island declaration(s) of `{crate_name}` not checked: {why} (`--all-rows` \
         lists them)",
        label("NOT CHECKED")
    )
}

/// `NOT MEASURED  <n> island declaration(s) of `<crate>` not measured this
/// run: <why>`: the one line that stands for the base rows, none failed, that
/// a unit that published nothing may hold.
fn not_measured_line(crate_name: &str, count: usize, why: &str) -> String {
    format!(
        "{}{count} island declaration(s) of `{crate_name}` not measured this run: {why}",
        label("NOT MEASURED")
    )
}

/// The island rows of `now` against `base` (the caller's last snapshot that
/// measured its islands, `islands_measured`), and the summary's island
/// counts; `None` when neither has an island section.
///
/// * Rows present on both sides are compared as obligation rows are
///   ([`compare_key`]); a row unchanged but not plainly proved prints as
///   `STILL` on every run, since no listing prints island rows. A key only
///   now has is `GAINED`, `NEW FAILED` or `NEW`.
/// * A base row missing now is `VANISHED` only where every proof unit of the
///   package published and now's section of its crate, if any, is complete.
///   Otherwise it is not a deleted claim: with a unit that published nothing,
///   the base rows that were not failed are one `NOT MEASURED` count line per
///   crate and a failed one prints on its own; with an island that did not
///   parse, each is `NOT MEASURED`.
/// * In a section that is not a measurement (`not_measured_because`) only
///   the refused rows and new keys are compared (`NEW FAILED`, `STILL`,
///   `NEW`), a row the base had failed that is not now is `CHANGED`, and
///   every other row is counted in one `NOT CHECKED` line naming why.
///
/// With no base, every row not plainly proved prints (in a section that is
/// not a measurement only the refused rows, the rest in the `NOT CHECKED`
/// line). `--all-rows` prints every row first.
fn island_rows(
    base: Option<&PackageObligations>,
    now: &PackageObligations,
    all_rows: bool,
) -> Option<(Vec<String>, IslandSummary)> {
    let base = base.filter(|base| islands_measured(base));
    let islands = &now.clean_islands;
    if islands.sections.is_empty() && base.is_none_or(|base| base.clean_islands.sections.is_empty())
    {
        return None;
    }
    let mut summary = IslandSummary {
        total: islands.sections.values().map(|section| section.rows.len()).sum(),
        problems: islands
            .sections
            .iter()
            .flat_map(|(crate_name, section)| {
                section.problems.iter().map(move |problem| format!("{crate_name}: {problem}"))
            })
            .collect(),
        not_measured: islands.units_problem(),
        any_section: !islands.sections.is_empty(),
        ..IslandSummary::default()
    };
    let mut lines: Vec<String> = Vec::new();
    if all_rows {
        lines.extend(
            islands
                .sections
                .values()
                .flat_map(|section| section.rows.values())
                .map(|decl| row("", &decl.record, None, false)),
        );
    }
    let empty: BTreeMap<String, CleanDeclRecord> = BTreeMap::new();
    let Some(base) = base else {
        for (crate_name, section) in &islands.sections {
            let why = not_measured_because(islands, Some(section));
            let mut not_checked = 0;
            for decl in section.rows.values() {
                if why.is_some() && !decl.record.is_failed() {
                    not_checked += 1;
                } else if !all_rows && !decl.record.is_plainly_proved() {
                    lines.push(row("", &decl.record, None, false));
                }
            }
            if let Some(why) = why.filter(|_| not_checked > 0) {
                lines.push(not_checked_line(crate_name, not_checked, &why));
            }
        }
        return Some((lines, summary));
    };
    let mut rows: Vec<(usize, String)> = Vec::new();
    let mut changed = 0;
    // `counted`: whether the line is a row that changed (a `STILL` row or a
    // count line is not).
    let mut push = |word: &str, line: String, counted: bool| {
        changed += usize::from(counted);
        rows.push((ORDER.iter().position(|w| *w == word).expect("a row word"), line));
    };
    let crates: BTreeSet<&String> =
        islands.sections.keys().chain(base.clean_islands.sections.keys()).collect();
    for crate_name in crates {
        let section = islands.sections.get(crate_name);
        let now_rows = section.map_or(&empty, |section| &section.rows);
        let base_rows =
            base.clean_islands.sections.get(crate_name).map_or(&empty, |section| &section.rows);
        let why = not_measured_because(islands, section);
        // A key missing now is one no unit has: every unit published, and
        // this crate's section, if any, enumerated every declaration.
        let vanished = islands.units_whole() && section.is_none_or(|section| section.complete);
        let mut not_checked = 0;
        let mut not_measured = 0;
        for (key, after) in now_rows {
            let after = &after.record;
            match base_rows.get(key).map(|before| &before.record) {
                Some(before) if why.is_some() && !after.is_failed() => {
                    if before.is_failed() {
                        push("CHANGED", row("CHANGED", after, Some(before), false), true);
                    } else {
                        not_checked += 1;
                    }
                }
                Some(before) => match compare_key(before, after) {
                    Some(word) => push(word, row(word, after, Some(before), false), true),
                    None if !after.is_plainly_proved() => {
                        push("STILL", row("STILL", after, None, false), false);
                    }
                    None => {}
                },
                None => {
                    let word = new_key(after);
                    push(word, row(word, after, None, true), true);
                }
            }
        }
        for (key, before) in base_rows {
            if now_rows.contains_key(key) {
                continue;
            }
            let before = &before.record;
            if vanished {
                push(
                    "VANISHED",
                    format!(
                        "{:<12}{}  {}  (was {})  {}",
                        "VANISHED",
                        before.key,
                        before.kind,
                        before.status,
                        before.location_label()
                    ),
                    true,
                );
            } else if !islands.units_whole() && !before.is_failed() {
                not_measured += 1;
            } else {
                push(
                    "NOT MEASURED",
                    format!(
                        "{}{}  {}  not measured this run (was {})  {}",
                        label("NOT MEASURED"),
                        before.key,
                        before.kind,
                        before.status,
                        before.location_label()
                    ),
                    true,
                );
            }
        }
        if let Some(why) = why.filter(|_| not_checked > 0) {
            push("NOT CHECKED", not_checked_line(crate_name, not_checked, &why), false);
        }
        if let Some(units) = islands.units_problem().filter(|_| not_measured > 0) {
            push("NOT MEASURED", not_measured_line(crate_name, not_measured, &units), false);
        }
    }
    rows.sort();
    lines.extend(rows.into_iter().map(|(_, line)| line));
    summary.changed = Some(changed);
    Some((lines, summary))
}

/// The base a caller's pointer names, or `None`; `which` names the pointer in
/// a note (empty, `concluded ` or `islands `). A pointer that is not there,
/// or that nobody wrote for [`POINTER_RETENTION`] (whether or not a prune has
/// removed it yet), gives no base and says nothing: for the plain pointer a
/// first run; for `.concluded` or `.islands`, no run of the caller that
/// concluded or measured its islands within the retention, however recently
/// the caller ran. One that cannot be read,
/// does not hold a token (`load` refuses it, so a pointer never names a path)
/// or names a snapshot that is gone or unreadable is noted, with no base.
fn read_pointer(
    dir: &Path,
    pointer: &Path,
    package: &str,
    which: &str,
    notes: &mut Vec<String>,
) -> Option<(String, PackageObligations)> {
    if older_than(pointer, POINTER_RETENTION, SystemTime::now()) {
        return None;
    }
    let token = match std::fs::read_to_string(pointer) {
        Ok(text) => text.trim().to_string(),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return None,
        Err(error) => {
            notes.push(format!(
                "your {which}pointer `{}` for `{package}` cannot be read ({error}); no base",
                pointer.display()
            ));
            return None;
        }
    };
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
/// what changed: the status, else the stop, else the label, else the failure
/// basis (which an `ASSUMED`, `CONTRACT` or `CONDITIONAL` label does not
/// show), else the grade. A `new` row (`new` true) says `(new)`; a `STILL` row
/// and an `--all-rows` row say nothing.
fn row(word: &str, record: &ObligationRecord, was: Option<&ObligationRecord>, new: bool) -> String {
    let was = match was {
        Some(old) if old.status != record.status => format!(" (was {})", old.status),
        Some(old) if old.stop != record.stop => format!(" (was stopped by {})", old.stop),
        Some(old) if old.listing_label() != record.listing_label() => {
            format!(" (was [{}])", old.listing_label())
        }
        Some(old) if old.basis != record.basis => {
            format!(" (was basis {})", old.basis.as_deref().unwrap_or("-"))
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
    /// the lines' own text: the rows that carry the listing's label sort by
    /// it (so a failed row before an unknown one), then by key.
    pub(crate) lines: Vec<String>,
    /// How many obligation rows changed: one per row line, and a `REMOVED`
    /// line counts its function's obligations. A `RUN`, `STILL` or `MOVED`
    /// line counts none: a move pairs the function, and its rows that changed
    /// are counted on their own lines.
    pub(crate) rows: usize,
    /// How many rows the base had that have no row now: a `REMOVED`
    /// function's obligations, each `VANISHED` row and each `LOST` row whose
    /// key vanished. With this run's rows they are the `M` that `rows` is
    /// out of.
    pub(crate) gone: usize,
}

/// The rows that changed between `base` and `now`, in functions paired as the
/// baseline pairs them ([`pair_functions`]) and by local id ([`compare_key`]),
/// and, with `still`, a `STILL` row for every row unchanged but not plainly
/// proved.
pub(crate) fn changed_rows(
    base: &PackageObligations,
    now: &PackageObligations,
    still: bool,
) -> Changes {
    changes(base, now, still, true)
}

/// [`changed_rows`], or, with `compare_obligations` false (`now` did not
/// conclude), only the header facts that moved and, with `still`, every row of
/// `now` not plainly proved as a `STILL` row: no row is counted changed or
/// gone.
fn changes(
    base: &PackageObligations,
    now: &PackageObligations,
    still: bool,
    compare_obligations: bool,
) -> Changes {
    // (order, line), and how many obligation rows each line stands for.
    let mut rows: Vec<(usize, String)> = Vec::new();
    let mut changed = 0;
    let mut gone = 0;
    let mut push = |word: &str, line: String, count: usize| {
        let order = ORDER.iter().position(|w| *w == word).expect("a row word");
        changed += count;
        rows.push((order, line));
    };
    for (field, old, new) in [
        ("outcome", base.outcome.as_str(), now.outcome.as_str()),
        ("targo_trust_commit", base.targo_trust_commit.as_str(), now.targo_trust_commit.as_str()),
        ("profile", base.profile.as_str(), now.profile.as_str()),
    ] {
        if old != new {
            push("RUN", format!("{:<12}{field} {old} -> {new}", "RUN"), 0);
        }
    }
    if base.coverage_complete != now.coverage_complete {
        push(
            "RUN",
            format!(
                "{:<12}coverage_complete {} -> {}",
                "RUN", base.coverage_complete, now.coverage_complete
            ),
            0,
        );
    }
    if !compare_obligations {
        // A run that did not conclude measured no obligation: none is compared,
        // and, with `still`, every row it has that is not plainly proved
        // prints, as it does on every run.
        for after in now.obligations.iter().filter(|after| still && !after.is_plainly_proved()) {
            push("STILL", row("STILL", after, None, false), 0);
        }
        rows.sort();
        return Changes {
            lines: rows.into_iter().map(|(_, line)| line).collect(),
            rows: 0,
            gone: 0,
        };
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
            gone += old.obligations.len();
            push(
                "REMOVED",
                format!("{:<12}{old_path}  ({} obligation(s))", "REMOVED", old.obligations.len()),
                old.obligations.len(),
            );
            continue;
        };
        claimed.insert(new_path);
        let new = &new_functions[new_path];
        if new_path != old_path {
            push(
                "MOVED",
                format!("{:<12}{old_path} -> {new_path}  (paired by {})", "MOVED", how.as_str()),
                0,
            );
        }
        // `Some(changed)` when both sides state a source digest; `None` when
        // either does not, which counts as unchanged, as in the baseline.
        let digests = match (&old.source, &new.source) {
            (Some(before), Some(after)) => Some(before != after),
            _ => None,
        };
        let source_changed = digests == Some(true);
        for (id, before) in &old.obligations {
            match new.obligations.get(id) {
                Some(after) => match compare_key(before, after) {
                    Some(word) => push(word, row(word, after, Some(before), false), 1),
                    None if still && !after.is_plainly_proved() => {
                        push("STILL", row("STILL", after, None, false), 0)
                    }
                    None => {}
                },
                None if before.is_proved() && !source_changed => {
                    gone += 1;
                    let why = if digests.is_some() {
                        "its function's source did not change"
                    } else {
                        "its function's source digest is not stated on both sides"
                    };
                    push(
                        "LOST",
                        format!(
                            "{:<12}{}  {}  vanished (was proved; {why})  -  {}",
                            "LOST",
                            before.key,
                            before.kind,
                            before.location_label()
                        ),
                        1,
                    )
                }
                None => {
                    gone += 1;
                    push(
                        "VANISHED",
                        format!(
                            "{:<12}{}  {}  (was {})  {}",
                            "VANISHED",
                            before.key,
                            before.kind,
                            before.status,
                            before.location_label()
                        ),
                        1,
                    )
                }
            }
        }
        for (id, after) in &new.obligations {
            if !old.obligations.contains_key(id) {
                let word = new_key(after);
                push(word, row(word, after, None, true), 1);
            }
        }
    }
    for (new_path, new) in &new_functions {
        if claimed.contains(new_path.as_str()) {
            continue;
        }
        for after in new.obligations.values() {
            let word = new_key(after);
            push(word, row(word, after, None, true), 1);
        }
    }
    rows.sort();
    Changes { lines: rows.into_iter().map(|(_, line)| line).collect(), rows: changed, gone }
}

/// The word of a key present on both sides, or `None` when nothing the record
/// states about it changed but its location. Same status and stop with
/// another grade, basis or label is `CHANGED`: a proof that now rests on a new
/// premise is not the proof the base had. So is a stop change of a row proved
/// on both sides: `GAINED` is a proof the base did not have.
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
    } else if after.is_proved() && !before.is_proved() {
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

/// The target directory whose `trust/obligations/` holds the record at `path`
/// (`crate::obligations::records_dir`), canonical, so that two spellings of one
/// directory are one; `None` when it is not there.
fn target_dir_of_record(path: &Path) -> Option<PathBuf> {
    let parent = path.parent().filter(|parent| !parent.as_os_str().is_empty());
    let records = std::fs::canonicalize(parent.unwrap_or(Path::new("."))).ok()?;
    let trust = records.parent()?;
    if records.file_name()? != "obligations" || trust.file_name()? != "trust" {
        return None;
    }
    Some(trust.parent()?.to_path_buf())
}

/// Refuse a record whose rows the view could not show: a row whose key is not
/// `<def path>#<id>` is never matched with a base row, and of a key held twice
/// only the last row is (`functions_of` keeps one row per local id), so such a
/// row would print with no base and vanish once there is one. A check never
/// writes either.
fn keyed_once(record: &PackageObligations) -> Result<(), String> {
    let mut seen = BTreeSet::new();
    for obligation in &record.obligations {
        if split_obligation_key(&obligation.key).is_none() {
            return Err(format!(
                "obligation key `{}` is not `<def path>#<16 lowercase hex digits>`",
                obligation.key
            ));
        }
        if !seen.insert(obligation.key.as_str()) {
            return Err(format!("obligation key `{}` appears twice", obligation.key));
        }
    }
    Ok(())
}

/// `targo trust delta`: snapshot `trust.obligations.v1` records already on
/// disk (a check's, or a test run's snapshot), one per package, and print the
/// view ([`publish`]) without re-running anything; its `--help` says which base and target directory it
/// uses. Exit 0, or 2 for a usage error, a record that cannot be read or that
/// the view could not show, a package named twice, or no target directory.
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
        // The `.lean` lane's rule for the same flag (`lean_cli::parse`): one
        // directory, given once, not empty and not starting with `-`, in
        // either spelling.
        let value = if arg == "--target-dir" {
            index += 1;
            match args.get(index) {
                Some(dir) => Some(dir.as_str()),
                None => {
                    eprintln!("targo trust delta: --target-dir requires a directory");
                    return ExitCode::from(2);
                }
            }
        } else {
            arg.strip_prefix("--target-dir=")
        };
        if let Some(dir) = value {
            if dir.is_empty() || dir.starts_with('-') || target_dir.is_some() {
                eprintln!("targo trust delta: --target-dir requires exactly one directory");
                return ExitCode::from(2);
            }
            target_dir = Some(PathBuf::from(dir));
        } else if arg == "--help" || arg == "-h" {
            println!(
                "usage: targo trust delta [--since <token>] [--all-rows] [--target-dir <dir>] \
                 <record.ndjson>...\n\
                 Snapshot `trust.obligations.v1` records already on disk, one per package (a \
                 check's, <target-dir>/trust/obligations/*.ndjson, or a test run's, kept only \
                 as its snapshot <target-dir>/trust/snapshots/<token>), and print the rows \
                 that changed since a base measured on the same lane, policy and selection (a \
                 test run's record: also given the same harness arguments): with --since, the \
                 snapshot <token> names (its package only; the \
                 others have none), else the last such token this session (ATERM_SESSION_ID, \
                 CLAUDE_CODE_SESSION_ID) was shown for that package within {days} days; with \
                 neither variable set, only --since gives a base. Every row not plainly proved \
                 prints, and --all-rows prints every row. Snapshots and session pointers are \
                 kept under --target-dir, else the target directory holding the records, else \
                 the one a `.lean` check would use here.",
                days = POINTER_RETENTION.as_secs() / (24 * 60 * 60)
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
    let mut packages = BTreeSet::new();
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
        let record = match parse_package_ndjson(&text) {
            Ok(record) => record,
            Err(error) => {
                eprintln!("targo trust delta: `{}`: {error}", path.display());
                return ExitCode::from(2);
            }
        };
        if let Err(error) = keyed_once(&record) {
            eprintln!("targo trust delta: `{}`: {error}", path.display());
            return ExitCode::from(2);
        }
        // Two records of one package would both diff against the one base
        // the run read before storing either.
        if !packages.insert(record.package.clone()) {
            eprintln!(
                "targo trust delta: `{}` is a record of package `{}`, and so is an earlier one; \
                 name one record per package",
                path.display(),
                record.package
            );
            return ExitCode::from(2);
        }
        records.push((record.package, text));
    }
    let target_dir = match target_dir {
        Some(dir) => dir,
        None => {
            let held: BTreeSet<Option<PathBuf>> =
                paths.iter().map(|path| target_dir_of_record(path)).collect();
            match held.into_iter().collect::<Vec<_>>().as_slice() {
                [Some(dir)] => dir.clone(),
                _ => match crate::lean_cli::records::record_target_dir(None) {
                    Ok(Some(dir)) => {
                        println!(
                            "note: the records named are not all under one \
                             `<target-dir>/trust/obligations/`; snapshots are kept under {} \
                             (pass --target-dir <dir> to choose)",
                            snapshots_dir(&dir).display()
                        );
                        dir
                    }
                    Ok(None) => {
                        eprintln!(
                            "targo trust delta: the records named are not all under one \
                             `<target-dir>/trust/obligations/`, and no CARGO_TARGET_DIR, \
                             CARGO_BUILD_TARGET_DIR or Cargo workspace here names another; pass \
                             --target-dir <dir>"
                        );
                        return ExitCode::from(2);
                    }
                    Err(error) => {
                        eprintln!("targo trust delta: {error}");
                        return ExitCode::from(2);
                    }
                },
            }
        }
    };
    let caller = caller_session_from_env();
    let view = publish(&target_dir, &records, &request, caller.as_deref(), true);
    for line in view.lines() {
        println!("{line}");
    }
    for note in view.commit_pointers() {
        println!("note: {note}");
    }
    ExitCode::SUCCESS
}

#[cfg(test)]
#[path = "agent_delta_tests.rs"]
mod tests;
