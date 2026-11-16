// targo-trust/meter.rs: `targo trust meter` — where an agent's time went
// (edit-loop plan step 1, METER; docs/design/2026-11-12-live-edit-loop.md).
//
// The meter computes nothing new. It reads the timing the toolchain already
// records and prints it as one table, largest wait first:
//
//  * `trust.package.v1` (`<target-dir>/trust/packages/*.json`, written by every
//    crate-mode `targo trust check`): the package's `cost.wall_clock_ms`, the
//    sum of the `time_ms` the compiler reported on the package's rows. A
//    row's `time_ms` is the time the engine that decided it reported for that
//    one obligation (a solver's, a kernel replay's, or a timeout's budget), so
//    the sum holds no load, standard-library decode or obligation generation.
//    The obligation lines of `trust.obligations.v1` carry no time (they are a
//    function of the inputs alone), so this sum is the only Rust proof time a
//    record holds. No timer spans a compiler phase (load, standard-library
//    decode, obligation generation, solving, kernel check): each package
//    names them as not measured, so its total is not the whole of its wait.
//  * `trust.lean-run.v1` (`<target-dir>/trust/lean/*.json`, written by a
//    `targo trust check <file.lean>` that runs its batch, whenever a target
//    directory resolves, `lean_cli::records::record_target_dir`; outside
//    every workspace with no `--target-dir`, `CARGO_TARGET_DIR` or
//    `CARGO_BUILD_TARGET_DIR` it writes none, and a failed write is only a
//    warning; `lean_cli::run_record`): the fresh session's start (the kernel
//    prelude), Clean's per-command records (an import's or lexical
//    command's time, or a declaration's elaboration with its kernel check as
//    one span), and the whole batch.
//    Per-declaration time is measured only when every declaration the batch
//    registered (the record names them) is timed; otherwise the phase is not
//    measured, naming the untimed ones, and the derived remainder
//    carries their elaboration and kernel check (below). Clean's module batch,
//    which the lane runs, records no declaration through that timer yet, so
//    today every run names the phase.
//  * The landing gate's run records (`<git-common-dir>/trust-land/runs/*/
//    record.json`, `scripts/land_gate.py`): the run's total (`seconds`), each
//    leg that ran, the checkout reads the run made (before and between legs,
//    and around the push), the Git-state guard read at each checkout boundary
//    that reads one (`guard_seconds`; a `land` run's own passes around its
//    push read none), and the checkout worker start-up, which runs before the
//    run's clock starts and so is not inside `seconds`; the meter adds it to
//    the run's wait. A checkout read is a pass the gate ran at a boundary (a
//    row with no `reused`): every tracked file of the checkout and its
//    populated submodules on an ordinary run, fewer on an IR-cohort diagnostic
//    run or when the pass refused early; a boundary the last complete pass
//    answered (`reused`, no file read) is counted apart as a reused boundary,
//    never as a read. The gate's other waits before its clock starts, such as
//    build-slot admission, are in no record and are listed as not recorded
//    ([`NOT_RECORDED`]). A `seconds` longer than any run since gate records
//    began ([`GATE_RECORDS_SINCE_UNIX_S`]) is not a wall time and is named as
//    not measured. The gate makes a run's directory after planning, so a run
//    that ends before that leaves nothing under `runs/` and is listed as not
//    recorded. It writes record.json only at the end of a run that does not
//    stop on an error, so a run directory without one (interrupted,
//    cancelled, still running, or stopped by an error; judged
//    against `--window` by its newest file) is named as not measured. A leg
//    with no exit did not run in the gate and has no row: one that did not
//    run waited for nothing, and the `targo-trust` leg `land` handed to a
//    push that ran ([`PUSHED_LEG`]) names its time as not measured. A leg
//    that runs several rows (push-rows' push-profile rows, a suite's targets
//    or members) has only its total in the record, so its per-row time is
//    named as not measured; only a leg that is one check
//    (`SINGLE_CHECK_LEGS`) has its row's time. The record keeps the ordinary
//    push step's exit (and its reason when the gate refused or failed the
//    push) and not its time.
//  * The pre-push hook's `TIMING:` lines (`scripts/hooks/pre-push`), from a
//    log the caller names: each phase, and each lane and each replay of an
//    inherited red marked with the phase that contains it (its line precedes
//    its phase's line), and `hook-before-verdict` as the hook's total up to
//    its verdict. A log may hold several hook runs. A run's first `TIMING:`
//    line is its `phase=prepare` line, written after the hook's refusals
//    before any lane, so a run refused there writes none, and the steps
//    after `hook-before-verdict` have no line: both are listed as not
//    recorded ([`NOT_RECORDED`]). A run whose lines end without
//    `hook-before-verdict`, at the next run's `prepare` line or at the log's
//    end, stopped before its verdict: its total is named as not measured,
//    and a lane or replay line it left with no phase line after it is marked
//    `(in an unfinished phase)`. A lane's or replay's time is part of its
//    phase's, so those rows and phase rows do not add up to the hook's total.
//
// A row the meter derives says so: `gate other (derived)` is the run's total
// less its legs, checkout reads and guard (the rest of the run, such as host
// measurement, selection, discovery and planning, hashing the toolchain and
// the stage 1 for cache keys, cache lookups and stores, judging leg logs,
// and any push less the checkout reads made during it), and
// `lean other (derived)` the batch's total less its session start and timed
// records (reading operands, the import closure, binding). While a
// declaration the batch registered is untimed, the batch registered and timed
// none after a recorded session start, or the record does not name what it
// registered, that remainder may also hold declarations' elaboration and
// kernel check, and the row is named `lean other incl. elaboration+kernel
// check (derived)` (`incl. untimed …` when the record names what it
// registered and some declaration is timed) so nobody reads
// it as overhead; a batch that registered and timed nothing with no recorded
// session start elaborated nothing and keeps the plain name. Coverage is
// judged only against the record's `registered` names: a declaration the
// batch elaborated but neither registered nor timed stays in the plain-named
// remainder, unnamed, and `--check` can still exit 0 (docs/PLAN.md
// PKG-LIVE-1, not on yet; no record a check writes today reaches this, since
// Clean's module batch times no declaration). A phase a source cannot supply
// is listed under "not measured" with the reason, never filled in: `--check`
// exits 0 only when every source it read yields a measured value for every
// phase it knows, and 1 naming each missing phase otherwise. Landed changes
// are counted from gate records whose ordinary push exited 0; per agent-hour
// and per processor-hour, and the work nobody read, are not derivable from
// any record yet and are reported absent.
//
// `--json` is one canonical JSON object (keys sorted, one LF at the end),
// schema `trust.meter.v1`, with `{"absent":…,"until":…}` for what no record
// can fill — the style of `trust.package.v1`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use serde_json::Value;

/// The schema name of the `--json` output.
pub(crate) const METER_SCHEMA: &str = "trust.meter.v1";

/// The gate record schema this meter reads (`scripts/land_gate.py` `SCHEMA`).
const GATE_RECORD_SCHEMA: &str = "trust-land-gate/2";

/// A verifying compile's internal phases. No timer spans any of them: solving
/// and kernel check are timed only per obligation (a row's `time_ms` is the
/// deciding engine's time for it: a solver's, a kernel replay's, or a
/// timeout's budget; `rust proof (row time_ms sum)` adds them up), and the
/// other phases not at all.
const COMPILER_PHASES: [&str; 5] =
    ["load", "std-decode", "obligation-generation", "solving", "kernel-check"];

/// Why a compiler phase has no value.
const COMPILER_PHASES_WHY: &str =
    "not measured: needs compiler phase timers (PKG-LIVE-1 remaining)";

/// Why a Lean run that registered declarations has no per-declaration time.
const LEAN_DECLARATIONS_UNTIMED: &str = "not measured: Clean's module batch, which `.lean` \
     checks and islands run through, times no declaration (clean_elab::DeclTiming sits on the \
     per-declaration registration entry the batch uses only for lexical commands); needs a \
     timer in clean's module_batch (PKG-LIVE-1 remaining)";

/// The reason when the record times a declaration but not every registered
/// one: not "times no declaration", which would contradict the timed rows.
const LEAN_DECLARATIONS_PARTLY_TIMED: &str = "not measured: Clean's module batch did not time \
     every declaration it registered (clean_elab::DeclTiming reaches a declaration only through \
     the per-declaration registration entry); needs a timer in clean's module_batch for every \
     declaration (PKG-LIVE-1 remaining)";

/// Untimed declaration names a reason lists before it counts the rest.
const NAMES_LISTED: usize = 5;

/// `a, b, c` — or the first [`NAMES_LISTED`] and `+N more`.
fn name_list(names: &[&str]) -> String {
    let mut listed = names.iter().take(NAMES_LISTED).copied().collect::<Vec<_>>().join(", ");
    if names.len() > NAMES_LISTED {
        listed.push_str(&format!(" +{} more", names.len() - NAMES_LISTED));
    }
    listed
}

/// Gate legs the meter knows to be one check, so the leg's time is that
/// row's time. Any other leg that ran (push-rows, a suite of test targets, a
/// member set, and any leg this list does not name) may run several rows, and
/// record.json keeps only the leg's total; a development leg that runs a
/// single test is not on this list, so its row time is named not measured.
const SINGLE_CHECK_LEGS: [&str; 5] =
    ["compiler-check", "tidy", "tcb-panic-ratchet", "ir-cohort", "olean-audit"];

/// Why a gate leg of several rows has no per-row time.
const GATE_ROWS_UNTIMED: &str = "record.json keeps only the leg's total `seconds`; needs \
     per-row time in scripts/land_gate.py's run record (PKG-LIVE-1 remaining)";

/// The leg `land` hands to the ordinary push instead of running it
/// (`scripts/land_gate.py` `defer_targo`): its entry has no exit or time, and
/// a record whose push ran carries `live_targo`, the push coordinator's
/// receipt, which has no time either.
const PUSHED_LEG: &str = "targo-trust";

/// Why [`PUSHED_LEG`] has no time when `land` handed it to the push.
const PUSHED_LEG_UNTIMED: &str = "`land` handed the leg to the ordinary push (`live_targo`), \
     whose pre-push hook runs it; record.json keeps no exit or time for it, so any time it took \
     is inside the push's, in `gate other`";

/// Why a gate run directory without a record.json has no time.
const RUN_WITHOUT_RECORD: &str = "run left no record.json (interrupted, still running, or \
     stopped by an error before writing it); its time is not measured";

/// No landing-gate run record was written before this time (2026-01-01
/// 00:00 UTC), so a record's `seconds` longer than the time from it to the
/// record's write is not the run's wall time. Before land_gate.py's clock fix
/// the gate's development and source-diagnostic runs wrote epoch minus uptime
/// there (about 1.79e9 s).
const GATE_RECORDS_SINCE_UNIX_S: u64 = 1_767_225_600;

/// Waits no source the meter reads records yet: an agent's own builds and
/// tests run outside the gate and the hook (the gate's and the hook's own
/// compile and test legs are rows); the gate's waits before its run clock
/// starts other than the checkout worker start-up (in `scripts/land_gate.py`,
/// among them `enter_admission` and `publication_lease`); a gate run that
/// ends before `_cmd_run_in_scope` makes its run directory, which leaves
/// nothing under `runs/`; and the pre-push hook's time outside its `TIMING:`
/// lines (`scripts/hooks/pre-push` writes its first, `phase=prepare`, after
/// its refusals before any lane, and none after `hook-before-verdict`, where
/// `launch_shadow` and, for the leg `land` hands it, `landing-hook-finish`'s
/// `checkout_problem` run).
const NOT_RECORDED: [&str; 6] = [
    "compiles outside the gate and the hook",
    "test runs outside the gate and the hook",
    "tool rebuilds",
    "the gate's waits before its run clock starts (such as build-slot admission and `land`'s \
     publication lease, but not its checkout start-up)",
    "gate runs that end before making their run directory",
    "the pre-push hook's time outside its `TIMING:` lines (a run refused before its \
     `phase=prepare` line, and the steps after `hook-before-verdict`: the shadow launch and, when \
     `land` hands the hook its `targo-trust` leg, `landing-hook-finish`'s checkout read)",
];

/// Rows the terminal table prints by default; `--top 0` prints every row.
const DEFAULT_TOP: usize = 20;

/// The largest record or log the meter reads.
const MAX_SOURCE_BYTES: usize = crate::input_limits::MAX_RELEASE_TRANSCRIPT_REPORT_BYTES;

const USAGE: &str = "\
Usage: targo trust meter [--target-dir DIR]... [--gate-runs DIR]... [--gate-record FILE]...
                         [--hook-log FILE]... [--window <N>h|<N>d] [--top N]
                         [--json | --format terminal|json] [--check]

Where an agent's time went, largest wait first, from the timing the toolchain
already records:
  --target-dir DIR    trust.package.v1 records (DIR/trust/packages/*.json, Rust proof time)
                      and trust.lean-run.v1 records (DIR/trust/lean/*.json, Lean session
                      start, import and command times, and the batch's remainder;
                      per-declaration time is not measured until Clean's module batch
                      records it)
  --gate-runs DIR     the landing gate's run records (DIR/*/record.json): per leg, checkout
                      reads (complete passes; reused boundaries counted apart) and
                      Git-state guard, the rest of the run, the checkout start-up before
                      it, and landed changes; a leg of several rows names its per-row
                      time as not measured, and so does a run directory with no
                      record.json
  --gate-record FILE  one gate run record
  --hook-log FILE     a pre-push hook log: its `TIMING:` lines, per phase, lane and
                      inherited-red replay; a hook run in it that stopped after its
                      `phase=prepare` line and before its verdict names its total as not
                      measured (a run refused before that line writes no `TIMING:` line)
  --window SPAN       only records written in the last SPAN (`12h`, `2d`); a hook log is
                      read whole
  --top N             table rows to print (default 20; 0 prints all)
  --json              one trust.meter.v1 JSON object instead of the table
  --format F          terminal (the default) or json; the last of --json and --format applies
  --check             exit 0 only when every source read yields a measured value for
                      every phase it knows; exit 1 naming each missing phase
  -h, --help          print this text

With no source named, the meter reads CARGO_TARGET_DIR, else CARGO_BUILD_TARGET_DIR,
else target/ in the workspace root that governs the current directory (none outside
every workspace), when it holds a trust/ directory, and this repository's
<git-common-dir>/trust-land/runs when it exists. A `build.target-dir` in a Cargo
config file is not read: name --target-dir for the records a check wrote there.
Exit: 1 --check found a phase not measured (a named source that is missing or empty
is one); 2 usage error, no source named and none found, or the default target
directory cannot be resolved (the gate runs are then not read either); else 0.";

/// One measured (or derived) wait.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    category: &'static str,
    phase: String,
    item: String,
    source: String,
    wait_us: u64,
    /// How many measurements were summed into this row.
    count: u64,
    /// A record's total less its measured parts, not a timer of its own.
    derived: bool,
}

/// One phase a source cannot supply, and why.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Missing {
    category: &'static str,
    phase: String,
    item: String,
    source: String,
    why: String,
}

/// One source the meter read.
#[derive(Debug, Clone)]
struct SourceSummary {
    kind: &'static str,
    path: String,
    category: &'static str,
    records: usize,
    /// The source's own total wait, when it records one.
    total_us: Option<u64>,
    /// A gate run's checkout boundaries: timed passes (reads) and reused
    /// boundaries, counted apart; None when the record has no
    /// `checkout_checks` array.
    checkout: Option<(usize, usize)>,
    /// The source names a wait of its own that `total_us` leaves out, so its
    /// total is not the whole of it.
    total_partial: bool,
}

/// Landed changes, from gate records.
#[derive(Debug, Clone, Default)]
struct Landed {
    gate_runs: usize,
    /// Run directories in the window that left no record.json: whether they
    /// landed anything is unknown.
    runs_without_record: usize,
    through_gate: usize,
    from_unix_s: Option<u64>,
    to_unix_s: Option<u64>,
}

#[derive(Debug, Default)]
struct Meter {
    rows: Vec<Row>,
    missing: Vec<Missing>,
    sources: Vec<SourceSummary>,
    /// Categories with a source whose total the meter could not read: a
    /// record or hook log that cannot be read or names another schema, and a
    /// gate run directory that left no record.json. No [`SourceSummary`]
    /// stands for them, and their wait is in no total.
    unread: std::collections::BTreeSet<&'static str>,
    landed: Landed,
}

#[derive(Debug, Default)]
struct Request {
    target_dirs: Vec<PathBuf>,
    gate_runs: Vec<PathBuf>,
    gate_records: Vec<PathBuf>,
    hook_logs: Vec<PathBuf>,
    window: Option<Duration>,
    top: Option<usize>,
    json: bool,
    check: bool,
    help: bool,
}

fn parse(args: &[String]) -> Result<Request, String> {
    let mut request = Request::default();
    let mut index = 0;
    while index < args.len() {
        let arg = args[index].as_str();
        let (flag, inline) = match arg.split_once('=') {
            Some((flag, value)) if flag.starts_with("--") => (flag, Some(value.to_string())),
            _ => (arg, None),
        };
        let mut value = |name: &str| -> Result<String, String> {
            if let Some(value) = &inline {
                return if value.is_empty() {
                    Err(format!("{name} requires a value"))
                } else {
                    Ok(value.clone())
                };
            }
            index += 1;
            match args.get(index) {
                Some(value) if !value.is_empty() && !value.starts_with("--") => Ok(value.clone()),
                _ => Err(format!("{name} requires a value")),
            }
        };
        match flag {
            "--target-dir" => request.target_dirs.push(PathBuf::from(value(flag)?)),
            "--gate-runs" => request.gate_runs.push(PathBuf::from(value(flag)?)),
            "--gate-record" => request.gate_records.push(PathBuf::from(value(flag)?)),
            "--hook-log" => request.hook_logs.push(PathBuf::from(value(flag)?)),
            "--window" => {
                if request.window.is_some() {
                    return Err("--window is given twice".into());
                }
                request.window = Some(parse_window(&value(flag)?)?);
            }
            "--top" => {
                let text = value(flag)?;
                let top = text
                    .parse::<usize>()
                    .map_err(|_| format!("--top takes a row count, not `{text}`"))?;
                request.top = Some(top);
            }
            "--json" if inline.is_none() => request.json = true,
            "--format" => match value(flag)?.as_str() {
                "json" => request.json = true,
                "terminal" => request.json = false,
                other => {
                    return Err(format!("the meter has no `{other}` format; use terminal or json"));
                }
            },
            "--check" if inline.is_none() => request.check = true,
            "--help" | "-h" if inline.is_none() => request.help = true,
            _ => return Err(format!("unknown argument `{arg}`")),
        }
        index += 1;
    }
    Ok(request)
}

fn parse_window(text: &str) -> Result<Duration, String> {
    let refuse = || format!("--window takes `<N>h` or `<N>d`, not `{text}`");
    let Some((cut, _)) = text.char_indices().last() else { return Err(refuse()) };
    let (number, unit) = text.split_at(cut);
    let count: u64 = number.parse().map_err(|_| refuse())?;
    let seconds = match unit {
        "h" => count.checked_mul(3600),
        "d" => count.checked_mul(86_400),
        _ => None,
    }
    .ok_or_else(refuse)?;
    if seconds == 0 {
        return Err(refuse());
    }
    Ok(Duration::from_secs(seconds))
}

/// `targo trust meter …`
pub(crate) fn run_subcommand(args: &[String]) -> ExitCode {
    let mut request = match parse(args) {
        Ok(request) => request,
        Err(error) => {
            eprintln!("targo trust meter: {error}\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    if request.help {
        println!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    let explicit = !(request.target_dirs.is_empty()
        && request.gate_runs.is_empty()
        && request.gate_records.is_empty()
        && request.hook_logs.is_empty());
    if !explicit {
        if let Err(error) = default_sources(&mut request) {
            eprintln!("targo trust meter: no default target directory: {error}\n{USAGE}");
            return ExitCode::from(2);
        }
        if request.target_dirs.is_empty() && request.gate_runs.is_empty() {
            eprintln!(
                "targo trust meter: no source: no target directory holding a trust/ directory \
                 and no gate run records here; name --target-dir, --gate-runs, --gate-record or \
                 --hook-log\n{USAGE}"
            );
            return ExitCode::from(2);
        }
    }
    let now = SystemTime::now();
    let meter = Meter::read(&request, now);
    if request.json {
        print!("{}", meter.render_json());
    } else {
        print!("{}", meter.render_terminal(request.top.unwrap_or(DEFAULT_TOP)));
    }
    if request.check {
        if meter.complete() {
            return ExitCode::SUCCESS;
        }
        eprintln!(
            "targo trust meter --check: {} phase(s) not measured:",
            meter.missing.len().max(1)
        );
        if meter.missing.is_empty() {
            eprintln!("  no source yielded a record");
        }
        for missing in &meter.missing {
            eprintln!("  {} {} ({}): {}", missing.phase, missing.item, missing.source, missing.why);
        }
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}

/// The sources a bare `targo trust meter` reads: the target directory a `.lean`
/// check would write (`lean_cli::records::record_target_dir`, which reads no
/// Cargo config file) when it holds a `trust/` directory, and this
/// repository's gate run records when their directory exists. An error
/// resolving that target directory is returned before the gate runs are looked
/// for, and the meter exits 2 on it.
fn default_sources(request: &mut Request) -> Result<(), String> {
    // Outside every workspace with no target directory named, no check wrote
    // a record this could read (`lean_cli::records::record_target_dir`).
    if let Some(target) = crate::lean_cli::records::record_target_dir(None)? {
        if target.join("trust").is_dir() {
            request.target_dirs.push(target);
        }
    }
    // Outside a Git repository there are no gate runs to read.
    let Ok(cwd) = std::env::current_dir() else { return Ok(()) };
    let Ok(root) = crate::controlled_git::resolve_repo_root(&cwd) else { return Ok(()) };
    let Ok(common) = crate::controlled_git::text(
        &root,
        &["rev-parse", "--git-common-dir"],
        "meter Git common-directory probe",
        64 * 1024,
        Duration::from_secs(30),
    ) else {
        return Ok(());
    };
    let common = Path::new(&common);
    let common = if common.is_absolute() { common.to_path_buf() } else { root.join(common) };
    let runs = common.join("trust-land").join("runs");
    if runs.is_dir() {
        request.gate_runs.push(runs);
    }
    Ok(())
}

fn micros_of_seconds(seconds: f64) -> Option<u64> {
    (seconds.is_finite() && seconds >= 0.0).then(|| (seconds * 1_000_000.0).round() as u64)
}

fn unix_seconds(time: SystemTime) -> Option<u64> {
    time.duration_since(UNIX_EPOCH).ok().map(|elapsed| elapsed.as_secs())
}

/// The newest modification time of `dir` and the entries directly in it (a
/// gate run directory holds its logs flat), `None` when none can be read.
fn newest_mtime(dir: &Path) -> Option<SystemTime> {
    let entries = std::fs::read_dir(dir).into_iter().flatten().flatten().map(|entry| entry.path());
    std::iter::once(dir.to_path_buf())
        .chain(entries)
        .filter_map(|path| std::fs::metadata(path).and_then(|metadata| metadata.modified()).ok())
        .max()
}

/// Files directly in `dir` with `extension`, sorted.
fn files_with_extension(dir: &Path, extension: &str) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .into_iter()
        .flatten()
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| path.is_file() && path.extension().is_some_and(|ext| ext == extension))
        .collect();
    files.sort();
    files
}

impl Meter {
    fn read(request: &Request, now: SystemTime) -> Self {
        let mut meter = Self::default();
        let since = request.window.and_then(|window| now.checked_sub(window));
        let in_window = |path: &Path| -> bool {
            let Some(since) = since else { return true };
            std::fs::metadata(path)
                .and_then(|metadata| metadata.modified())
                .is_ok_and(|modified| modified >= since)
        };
        for dir in &request.target_dirs {
            let packages = crate::package_record::package_records_dir(dir);
            let lean = crate::lean_cli::run_record::records_dir(dir);
            let package_files: Vec<PathBuf> = files_with_extension(&packages, "json")
                .into_iter()
                .filter(|path| in_window(path))
                .collect();
            let lean_files: Vec<PathBuf> = files_with_extension(&lean, "json")
                .into_iter()
                .filter(|path| in_window(path))
                .collect();
            if package_files.is_empty() && lean_files.is_empty() {
                meter.missing.push(Missing {
                    category: "proof",
                    phase: "records".into(),
                    item: "-".into(),
                    source: dir.display().to_string(),
                    why: format!(
                        "no trust.package.v1 record under {} and no trust.lean-run.v1 record \
                         under {}{}",
                        packages.display(),
                        lean.display(),
                        if since.is_some() { " in the window" } else { "" }
                    ),
                });
            }
            for path in package_files {
                meter.read_package_record(&path);
            }
            for path in lean_files {
                meter.read_lean_record(&path);
            }
        }
        let mut gate_files: Vec<PathBuf> = Vec::new();
        for dir in &request.gate_runs {
            let mut run_dirs: Vec<PathBuf> = std::fs::read_dir(dir)
                .into_iter()
                .flatten()
                .flatten()
                .map(|entry| entry.path())
                .filter(|path| path.is_dir())
                .collect();
            run_dirs.sort();
            let mut found: Vec<PathBuf> = Vec::new();
            let mut unrecorded = 0usize;
            for run in run_dirs {
                let record = run.join("record.json");
                if record.is_file() {
                    if in_window(&record) {
                        found.push(record);
                    }
                    continue;
                }
                // `scripts/land_gate.py` writes record.json only at the end
                // of a run that does not stop on an error, so an interrupted,
                // cancelled, failed or still-running run leaves logs and no
                // record. Its wait is real and unread:
                // name it, judged by its newest file's time (one whose time
                // cannot be read is named too).
                if since.is_some_and(|since| newest_mtime(&run).is_some_and(|time| time < since)) {
                    continue;
                }
                unrecorded += 1;
                meter.unread.insert("gate");
                meter.miss("gate", "records", "-", &run, RUN_WITHOUT_RECORD);
            }
            meter.landed.runs_without_record += unrecorded;
            if found.is_empty() && unrecorded == 0 {
                meter.missing.push(Missing {
                    category: "gate",
                    phase: "records".into(),
                    item: "-".into(),
                    source: dir.display().to_string(),
                    why: format!(
                        "no */record.json under it{}",
                        if since.is_some() { " in the window" } else { "" }
                    ),
                });
            }
            gate_files.extend(found);
        }
        for path in &request.gate_records {
            if in_window(path) {
                gate_files.push(path.clone());
            } else {
                // Named on the command line, so it is a source the meter was
                // pointed at: it yields nothing in the window, and says so.
                meter.miss(
                    "gate",
                    "records",
                    "-",
                    path,
                    "the record was not written in the window (or its file time cannot be read)",
                );
            }
        }
        for path in &gate_files {
            meter.read_gate_record(path);
        }
        for path in &request.hook_logs {
            meter.read_hook_log(path);
        }
        meter.rows.sort_by(|a, b| {
            b.wait_us
                .cmp(&a.wait_us)
                .then_with(|| a.category.cmp(b.category))
                .then_with(|| a.phase.cmp(&b.phase))
                .then_with(|| a.item.cmp(&b.item))
                .then_with(|| a.source.cmp(&b.source))
        });
        meter.missing.sort();
        meter.missing.dedup();
        meter
    }

    /// Add `wait_us` to the row of (category, phase, item, source), or start it.
    fn add(
        &mut self,
        category: &'static str,
        phase: &str,
        item: &str,
        source: &Path,
        wait_us: u64,
        derived: bool,
    ) {
        let source = source.display().to_string();
        if let Some(row) = self.rows.iter_mut().find(|row| {
            row.category == category
                && row.phase == phase
                && row.item == item
                && row.source == source
                && row.derived == derived
        }) {
            row.wait_us = row.wait_us.saturating_add(wait_us);
            row.count += 1;
            return;
        }
        self.rows.push(Row {
            category,
            phase: phase.to_string(),
            item: item.to_string(),
            source,
            wait_us,
            count: 1,
            derived,
        });
    }

    fn miss(&mut self, category: &'static str, phase: &str, item: &str, source: &Path, why: &str) {
        self.missing.push(Missing {
            category,
            phase: phase.to_string(),
            item: item.to_string(),
            source: source.display().to_string(),
            why: why.to_string(),
        });
    }

    /// Read one JSON record; a record that cannot be read or is not the named
    /// schema is a missing phase of its own, and its category's wait is not
    /// totalled.
    fn read_json(&mut self, path: &Path, category: &'static str, schema: &str) -> Option<Value> {
        let value = match crate::input_limits::read_bounded_utf8_file(path, MAX_SOURCE_BYTES) {
            Err(error) => Err(format!("cannot read it: {error}")),
            Ok(text) => serde_json::from_str::<Value>(&text)
                .map_err(|error| format!("not JSON: {error}"))
                .and_then(|value| {
                    let found = value.get("schema").and_then(Value::as_str).unwrap_or("");
                    if found == schema {
                        Ok(value)
                    } else {
                        Err(format!("names schema `{found}`, not `{schema}`"))
                    }
                }),
        };
        value
            .map_err(|why| {
                self.unread.insert(category);
                self.miss(category, "records", "-", path, &why);
            })
            .ok()
    }

    fn read_package_record(&mut self, path: &Path) {
        let Some(record) =
            self.read_json(path, "proof", crate::package_record::PACKAGE_RECORD_SCHEMA)
        else {
            return;
        };
        let package = record.get("package").and_then(Value::as_str).unwrap_or("?").to_string();
        let total_us = record
            .pointer("/cost/wall_clock_ms")
            .and_then(Value::as_u64)
            .map(|ms| ms.saturating_mul(1000));
        match total_us {
            Some(us) => {
                self.add("proof", "rust proof (row time_ms sum)", &package, path, us, false)
            }
            None => self.miss(
                "proof",
                "rust proof (row time_ms sum)",
                &package,
                path,
                "the record has no `cost.wall_clock_ms`",
            ),
        }
        // The row `time_ms` sum holds no load, std-decode or obligation
        // generation, which the compiler-phase rows below name as not
        // measured for this package: its total is never the whole of it.
        self.sources.push(SourceSummary {
            kind: "rust-package",
            path: path.display().to_string(),
            category: "proof",
            records: 1,
            total_us,
            checkout: None,
            total_partial: true,
        });
        for phase in COMPILER_PHASES {
            self.miss("proof", &format!("rust {phase}"), &package, path, COMPILER_PHASES_WHY);
        }
    }

    fn read_lean_record(&mut self, path: &Path) {
        let Some(record) =
            self.read_json(path, "lean", crate::lean_cli::run_record::LEAN_RUN_SCHEMA)
        else {
            return;
        };
        let files: Vec<&str> = record
            .get("files")
            .and_then(Value::as_array)
            .map(|files| files.iter().filter_map(Value::as_str).collect())
            .unwrap_or_default();
        let item = match files.as_slice() {
            [] => "?".to_string(),
            [one] => (*one).to_string(),
            [first, rest @ ..] => format!("{first} +{} more", rest.len()),
        };
        let total = record.pointer("/cost/wall_clock_us").and_then(Value::as_u64);
        let attempts =
            record.pointer("/cost/attempts").and_then(Value::as_array).cloned().unwrap_or_default();
        let mut session_us: Option<u64> = None;
        // Distinct declarations timed: an import-closure fixpoint can
        // elaborate one declaration in several attempts.
        let mut timed: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        let mut parts_us = 0u64;
        for attempt in &attempts {
            if let Some(us) = attempt.get("session_start_us").and_then(Value::as_u64) {
                session_us = Some(session_us.unwrap_or(0).saturating_add(us));
            }
            let declarations =
                attempt.get("declarations").and_then(Value::as_array).cloned().unwrap_or_default();
            for declaration in declarations {
                let name = declaration.get("name").and_then(Value::as_str).unwrap_or("?");
                let Some(us) = declaration.get("elapsed_us").and_then(Value::as_u64) else {
                    self.miss(
                        "lean",
                        "lean declaration",
                        name,
                        path,
                        "a declaration record has no `elapsed_us`",
                    );
                    continue;
                };
                let phase = match declaration.get("kind").and_then(Value::as_str) {
                    Some("declaration") => {
                        timed.insert(name.to_string());
                        "lean elaborate+kernel check"
                    }
                    Some("import") => "lean import",
                    _ => "lean command",
                };
                parts_us = parts_us.saturating_add(us);
                self.add("lean", phase, name, path, us, false);
            }
        }
        match session_us {
            Some(us) => {
                parts_us = parts_us.saturating_add(us);
                self.add("lean", "lean session start (prelude)", &item, path, us, false);
            }
            None => self.miss(
                "lean",
                "lean session start (prelude)",
                &item,
                path,
                "no attempt started a session (the batch was refused before elaboration)",
            ),
        }
        // Per-declaration time is measured only when every declaration the
        // batch registered, by name, has a timed `declaration` entry: a count
        // says nothing of which. A timed declaration the batch did not
        // register (refused by Trust's island policy, or nameless) is a row
        // of its own and stands in for no registered one. Otherwise the
        // remainder holds the untimed declarations' elaboration and kernel
        // check, and its row says so.
        let registered: Option<std::collections::BTreeSet<&str>> = record
            .get("registered")
            .and_then(Value::as_array)
            .and_then(|names| names.iter().map(Value::as_str).collect::<Option<_>>());
        let mut other_phase = "lean other (derived)";
        let why = match registered {
            Some(registered) if registered.is_empty() && timed.is_empty() => {
                Some(if session_us.is_some() {
                    // A session start is recorded, so the batch may have
                    // elaborated and refused every declaration: that time is
                    // in the remainder. `trust-certify`'s source batch also
                    // records the time of a session that failed to start.
                    other_phase = "lean other incl. elaboration+kernel check (derived)";
                    "the batch registered no declaration after its recorded session start (it \
                     refused each one or had none, or the session failed to start), so any \
                     declaration's elaboration and kernel check is untimed and inside the `lean \
                     other incl. elaboration+kernel check (derived)` row"
                        .to_string()
                } else {
                    "the batch registered no declaration: no attempt started a session, so it \
                     was refused before elaboration and elaborated none"
                        .to_string()
                })
            }
            Some(registered) => {
                let untimed: Vec<&str> =
                    registered.iter().copied().filter(|name| !timed.contains(*name)).collect();
                if untimed.is_empty() {
                    None
                } else {
                    // "Times no declaration" only when none was timed: a
                    // timed declaration the batch did not register is a row.
                    let (phase, reason) = if timed.is_empty() {
                        (
                            "lean other incl. elaboration+kernel check (derived)",
                            LEAN_DECLARATIONS_UNTIMED,
                        )
                    } else {
                        (
                            "lean other incl. untimed elaboration+kernel check (derived)",
                            LEAN_DECLARATIONS_PARTLY_TIMED,
                        )
                    };
                    other_phase = phase;
                    Some(format!(
                        "{reason} ({} of {} registered declaration(s) untimed: {})",
                        untimed.len(),
                        registered.len(),
                        name_list(&untimed)
                    ))
                }
            }
            None => {
                other_phase = "lean other incl. elaboration+kernel check (derived)";
                Some(format!(
                    "the record names no `registered` declarations, so {} timed \
                     declaration(s) cannot be judged complete",
                    timed.len()
                ))
            }
        };
        if let Some(why) = why {
            self.miss("lean", "lean elaborate+kernel check", &item, path, &why);
        }
        match total {
            Some(total) => {
                self.add("lean", other_phase, &item, path, total.saturating_sub(parts_us), true);
            }
            None => self.miss(
                "lean",
                "lean total",
                &item,
                path,
                "the record has no `cost.wall_clock_us`",
            ),
        }
        self.sources.push(SourceSummary {
            kind: "lean-run",
            path: path.display().to_string(),
            category: "lean",
            records: 1,
            total_us: total,
            checkout: None,
            total_partial: false,
        });
    }

    fn read_gate_record(&mut self, path: &Path) {
        let Some(record) = self.read_json(path, "gate", GATE_RECORD_SCHEMA) else {
            return;
        };
        self.landed.gate_runs += 1;
        if let Some(written) = std::fs::metadata(path)
            .and_then(|metadata| metadata.modified())
            .ok()
            .and_then(unix_seconds)
        {
            self.landed.from_unix_s =
                Some(self.landed.from_unix_s.map_or(written, |from| from.min(written)));
            self.landed.to_unix_s =
                Some(self.landed.to_unix_s.map_or(written, |to| to.max(written)));
        }
        // The run's total, or the one reason it has none: an absent
        // `seconds`, one that is no non-negative number, or one too long to
        // be a wall time each name `gate total` once.
        let written_unix_s = std::fs::metadata(path)
            .and_then(|metadata| metadata.modified())
            .ok()
            .and_then(unix_seconds)
            .or_else(|| unix_seconds(SystemTime::now()));
        let total: Result<u64, String> = match record.get("seconds") {
            None => Err("the record has no `seconds`".to_string()),
            Some(seconds) => seconds.as_f64().and_then(micros_of_seconds).ok_or_else(|| {
                format!(
                    "the record's `seconds` is `{seconds}`, not a non-negative number of seconds"
                )
            }),
        }
        .and_then(|us| {
            // No run since gate records began lasted longer than the time
            // from then to this record's write: such a `seconds` is not a
            // wall time.
            let Some(written) = written_unix_s else { return Ok(us) };
            let longest_s = written.saturating_sub(GATE_RECORDS_SINCE_UNIX_S);
            if us / 1_000_000 > longest_s {
                return Err(format!(
                    "`seconds` is {} s, longer than any run since gate records began ({} UTC); \
                     not a wall time (scripts/land_gate.py before its run-clock fix wrote epoch \
                     minus uptime there in development and source-diagnostic runs)",
                    us / 1_000_000,
                    utc(GATE_RECORDS_SINCE_UNIX_S)
                ));
            }
            Ok(us)
        });
        let mut parts_us = 0u64;
        if let Some(legs) = record.get("legs").and_then(Value::as_object) {
            for (leg, entry) in legs {
                // A leg that ran in the gate has an exit. Without one, the
                // leg `land` handed to a push that then ran (`live_targo`)
                // ran inside that push or not at all, with no time of its
                // own; any other leg did not run and waited for nothing.
                if entry.get("rc").is_none() {
                    if leg == PUSHED_LEG && record.get("live_targo").is_some() {
                        self.miss("gate", "gate leg", leg, path, PUSHED_LEG_UNTIMED);
                    }
                    continue;
                }
                match entry.get("seconds").and_then(Value::as_f64).and_then(micros_of_seconds) {
                    Some(us) => {
                        parts_us = parts_us.saturating_add(us);
                        self.add("gate", "gate leg", leg, path, us, false);
                    }
                    None => self.miss(
                        "gate",
                        "gate leg",
                        leg,
                        path,
                        "the leg ran (it has an exit) but the record has no `seconds` for it",
                    ),
                }
                if let Some(rows) = leg_rows(leg, entry) {
                    self.miss(
                        "gate",
                        "gate row time",
                        leg,
                        path,
                        &format!("{rows}; {GATE_ROWS_UNTIMED}"),
                    );
                }
            }
        } else {
            self.miss("gate", "gate legs", "-", path, "the record has no `legs`");
        }
        // A pass reads the checkout's tracked files; a reused boundary
        // (`reused` names the pass that answered it, `seconds` is 0.0) reads
        // none, so it is counted apart and never as a read. The Git-state
        // guard a `SourceBinding` boundary reads first (`guard_seconds`, on
        // its reused and complete rows alike) is a row of its own.
        let mut checkout = None;
        if let Some(checks) = record.get("checkout_checks").and_then(Value::as_array) {
            let mut reads_us = 0u64;
            let mut reads = 0usize;
            let mut reused = 0usize;
            let mut guard_us = 0u64;
            let mut guards = 0usize;
            for check in checks {
                let boundary = check.get("boundary").and_then(Value::as_str).unwrap_or("?");
                let is_reused = check.get("reused").is_some();
                if is_reused {
                    reused += 1;
                } else {
                    match check.get("seconds").and_then(Value::as_f64).and_then(micros_of_seconds) {
                        Some(us) => {
                            reads_us = reads_us.saturating_add(us);
                            reads += 1;
                        }
                        None => self.miss(
                            "gate",
                            "gate checkout read",
                            boundary,
                            path,
                            "the checkout read has no `seconds`",
                        ),
                    }
                }
                match check.get("guard_seconds") {
                    Some(value) => match value.as_f64().and_then(micros_of_seconds) {
                        Some(us) => {
                            guard_us = guard_us.saturating_add(us);
                            guards += 1;
                        }
                        None => self.miss(
                            "gate",
                            "gate checkout guard",
                            boundary,
                            path,
                            "`guard_seconds` is not a non-negative number of seconds",
                        ),
                    },
                    // A reused boundary always read the Git state, so its
                    // time is missing; a complete pass from a record written
                    // before the guard existed, or one outside `SourceBinding`
                    // (a `land` run's passes around its push), had none to time.
                    None if is_reused && check.get("git_state").is_some() => self.miss(
                        "gate",
                        "gate checkout guard",
                        boundary,
                        path,
                        "the reused boundary read the Git state but has no `guard_seconds`",
                    ),
                    None => {}
                }
            }
            if reads > 0 || reused > 0 {
                parts_us = parts_us.saturating_add(reads_us);
                let item = if reused > 0 {
                    format!("{reads} reads, {reused} reused boundaries")
                } else {
                    format!("{reads} reads")
                };
                self.add("gate", "gate checkout reads", &item, path, reads_us, false);
            }
            if guards > 0 {
                parts_us = parts_us.saturating_add(guard_us);
                self.add(
                    "gate",
                    "gate checkout guard",
                    &format!("{guards} guarded boundaries"),
                    path,
                    guard_us,
                    false,
                );
            }
            checkout = Some((reads, reused));
        }
        // The checkout worker pool starts before the run's clock
        // (`_checkout_workers_scope`), so its start-up is not inside
        // `seconds` and is added to the run's wait. `{}` is a run with no
        // pool. A record with no `checkout_startup` object may come from a
        // gate that started a pool and did not time it (0f70876a10a until
        // ac0bd4793de).
        let mut startup_total_us: Option<u64> = None;
        let startup_unread = match record.get("checkout_startup") {
            Some(Value::Object(startup)) => {
                let mut startup_us: Option<u64> = None;
                let mut unreadable = false;
                for key in ["python_seconds", "native_seconds"] {
                    let Some(value) = startup.get(key) else { continue };
                    match value.as_f64().and_then(micros_of_seconds) {
                        Some(us) => startup_us = Some(startup_us.unwrap_or(0).saturating_add(us)),
                        None => unreadable = true,
                    }
                }
                match startup_us {
                    Some(us) if !unreadable => {
                        startup_total_us = Some(us);
                        self.add("gate", "gate checkout start-up", "-", path, us, false);
                        None
                    }
                    None if startup.is_empty() => None,
                    _ => Some(
                        "`checkout_startup` has no finite `python_seconds` and `native_seconds`",
                    ),
                }
            }
            _ => Some(
                "the record has no `checkout_startup` object, so any checkout start-up is untimed",
            ),
        };
        // Outside `seconds`, so the run's wait lacks it.
        if let Some(why) = startup_unread {
            self.miss("gate", "gate checkout start-up", "-", path, why);
        }
        if let Some(push) = record.get("ordinary_push") {
            if push.get("rc").and_then(Value::as_i64) == Some(0) {
                self.landed.through_gate += 1;
            }
            // `scripts/land_gate.py` writes `ordinary_push` once the push step
            // passes its source check (`source_refusal("before ordinary
            // push")`, which leaves `source_refusal` and no `ordinary_push`),
            // a later refusal before any push included; the push's checkout
            // reads are in `checkout_checks`.
            self.miss(
                "gate",
                "gate ordinary push",
                "-",
                path,
                "record.json keeps the ordinary push step's exit (and its reason when the gate \
                 refused or failed the push), not its time; that time, less the checkout reads \
                 made during it, is inside `gate other`",
            );
        }
        match &total {
            Ok(total) => self.add(
                "gate",
                "gate other (derived)",
                "-",
                path,
                total.saturating_sub(parts_us),
                true,
            ),
            Err(why) => self.miss("gate", "gate total", "-", path, why),
        }
        self.sources.push(SourceSummary {
            kind: "gate-run",
            path: path.display().to_string(),
            category: "gate",
            records: 1,
            total_us: total.ok().map(|us| us.saturating_add(startup_total_us.unwrap_or(0))),
            checkout,
            total_partial: startup_unread.is_some(),
        });
    }

    fn read_hook_log(&mut self, path: &Path) {
        let bytes = match crate::input_limits::read_bounded_file(path, MAX_SOURCE_BYTES) {
            Ok(bytes) => bytes,
            Err(error) => {
                self.unread.insert("push");
                self.miss("push", "records", "-", path, &format!("cannot read it: {error}"));
                return;
            }
        };
        let text = String::from_utf8_lossy(&bytes);
        let mut lines = 0usize;
        let mut total: Option<u64> = None;
        let mut saw_total = false;
        // A wait of this log's that `total` leaves out: a run that stopped
        // before its verdict, or a verdict line with no elapsed time.
        let mut total_partial = false;
        // `TIMING:` lines of the current hook run: since the last
        // `hook-before-verdict`, or since the log's start or the current
        // run's `prepare` line. Above 0 at the end, the last run stopped
        // before its verdict.
        let mut after_total = 0usize;
        // Earlier runs that stopped before their verdict. `scripts/hooks/
        // pre-push` writes `phase=prepare` once per run, as its first
        // `TIMING:` line, so a `prepare` line while the current run has
        // lines starts a new run: the one before it ended with no verdict.
        let mut stopped_earlier = 0usize;
        // Lane and replay lines precede the line of the phase that ran them
        // (`run_fast_lanes`, `judge_inherited`, the scoped lanes): they wait
        // here until that phase names itself.
        let mut nested: Vec<(&'static str, String, Result<u64, String>)> = Vec::new();
        for line in text.lines() {
            let Some(fields) = parse_timing_line(line) else { continue };
            let phase = fields.get("phase").map(String::as_str).unwrap_or("?");
            if phase == "prepare" && after_total > 0 {
                self.add_nested(path, std::mem::take(&mut nested), "an unfinished phase");
                stopped_earlier += 1;
                after_total = 0;
            }
            lines += 1;
            after_total += 1;
            let lane = fields.get("lane").map(String::as_str).unwrap_or("-");
            let elapsed = match fields.get("elapsed_s").and_then(|value| value.parse::<u64>().ok())
            {
                Some(seconds) => Ok(seconds.saturating_mul(1_000_000)),
                None => Err(format!(
                    "elapsed_s={}",
                    fields.get("elapsed_s").map(String::as_str).unwrap_or("absent")
                )),
            };
            match phase {
                "lane" => nested.push(("push lane", lane.to_string(), elapsed)),
                "inherited-replay" => {
                    nested.push(("push inherited replay", lane.to_string(), elapsed));
                }
                "hook-before-verdict" => {
                    self.add_nested(path, std::mem::take(&mut nested), "an unnamed phase");
                    saw_total = true;
                    after_total = 0;
                    match elapsed {
                        Ok(us) => total = Some(total.unwrap_or(0).saturating_add(us)),
                        Err(why) => {
                            total_partial = true;
                            self.miss("push", "push hook total", "-", path, &why);
                        }
                    }
                }
                other => {
                    self.add_nested(path, std::mem::take(&mut nested), other);
                    let row_phase = format!("push {other}");
                    match elapsed {
                        Ok(us) => self.add("push", &row_phase, "-", path, us, false),
                        Err(why) => self.miss("push", &row_phase, "-", path, &why),
                    }
                }
            }
        }
        self.add_nested(path, nested, "an unfinished phase");
        let stopped_last = after_total > 0;
        let stopped = stopped_earlier + usize::from(stopped_last);
        total_partial |= stopped > 0;
        let why = if lines == 0 {
            self.miss("push", "push hook", "-", path, "the log holds no `TIMING:` line");
            None
        } else if stopped_earlier > 0 {
            let last = if stopped_last {
                format!(
                    ", and the last run, {after_total} `TIMING:` line(s), ends the log without one"
                )
            } else {
                String::new()
            };
            Some(format!(
                "{stopped} hook run(s) stopped before their verdict, so their totals are not in the \
                 hook total: {stopped_earlier} run(s) end at the next run's `phase=prepare` line \
                 with no `phase=hook-before-verdict` before it{last}"
            ))
        } else if !saw_total {
            Some(
                "no `TIMING: phase=hook-before-verdict` line (the hook stopped before its verdict)"
                    .to_string(),
            )
        } else if stopped_last {
            Some(format!(
                "the last hook run stopped before its verdict: {after_total} `TIMING:` line(s) \
                 follow the last `phase=hook-before-verdict`, and its total is not in the hook \
                 total"
            ))
        } else {
            None
        };
        if let Some(why) = why {
            self.miss("push", "push hook total", "-", path, &why);
        }
        self.sources.push(SourceSummary {
            kind: "hook-log",
            path: path.display().to_string(),
            category: "push",
            records: lines,
            total_us: total,
            checkout: None,
            total_partial,
        });
    }

    /// Rows for lanes and replays, each marked with the phase that ran it: a
    /// lane's time is inside its phase's, not beside it.
    fn add_nested(
        &mut self,
        path: &Path,
        nested: Vec<(&'static str, String, Result<u64, String>)>,
        within: &str,
    ) {
        for (kind, item, elapsed) in nested {
            let phase = format!("{kind} (in {within})");
            match elapsed {
                Ok(us) => self.add("push", &phase, &item, path, us, false),
                Err(why) => self.miss("push", &phase, &item, path, &why),
            }
        }
    }

    /// Every source read yielded a value for every phase it knows.
    fn complete(&self) -> bool {
        self.missing.is_empty() && !self.sources.is_empty()
    }

    /// Per category: the sum of its sources' own totals, and whether a source
    /// of it recorded none or only part of its own, or could not be read
    /// ([`Meter::unread`]).
    fn waited(&self) -> BTreeMap<&'static str, (u64, bool)> {
        let mut waited: BTreeMap<&'static str, (u64, bool)> = BTreeMap::new();
        for source in &self.sources {
            let entry = waited.entry(source.category).or_insert((0, false));
            match source.total_us {
                Some(us) => entry.0 = entry.0.saturating_add(us),
                None => entry.1 = true,
            }
            if source.total_partial {
                entry.1 = true;
            }
        }
        for &category in &self.unread {
            waited.entry(category).or_insert((0, false)).1 = true;
        }
        waited
    }

    fn render_json(&self) -> String {
        let waited: serde_json::Map<String, Value> = self
            .waited()
            .into_iter()
            .map(|(category, (us, partial))| {
                (
                    category.to_string(),
                    serde_json::json!({ "wait_us": us, "every_source_totalled": !partial }),
                )
            })
            .collect();
        let landed = if self.landed.gate_runs == 0 {
            crate::package_record::absent((
                "gate records",
                "landed changes are counted from gate run records; none was read",
            ))
        } else {
            serde_json::json!({
                "gate_runs": self.landed.gate_runs,
                "runs_without_record": self.landed.runs_without_record,
                "through_gate": self.landed.through_gate,
                "window": {
                    "from_unix_s": self.landed.from_unix_s,
                    "to_unix_s": self.landed.to_unix_s,
                },
                "outside_gate": crate::package_record::absent((
                    "push records",
                    "a push made outside the landing gate leaves no record the meter reads",
                )),
                "per_agent_hour": crate::package_record::absent(AGENT_HOURS_ABSENT),
                "per_processor_hour": crate::package_record::absent(PROCESSOR_HOURS_ABSENT),
            })
        };
        let value = serde_json::json!({
            "schema": METER_SCHEMA,
            "complete": self.complete(),
            "waited": waited,
            "not_recorded": NOT_RECORDED,
            "rows": self.rows.iter().map(|row| serde_json::json!({
                "category": row.category,
                "phase": row.phase,
                "item": row.item,
                "source": row.source,
                "wait_us": row.wait_us,
                "count": row.count,
                "derived": row.derived,
            })).collect::<Vec<_>>(),
            "not_measured": self.missing.iter().map(|missing| serde_json::json!({
                "category": missing.category,
                "phase": missing.phase,
                "item": missing.item,
                "source": missing.source,
                "why": missing.why,
            })).collect::<Vec<_>>(),
            "sources": self.sources.iter().map(|source| {
                let mut entry = serde_json::json!({
                    "kind": source.kind,
                    "path": source.path,
                    "records": source.records,
                    "total_us": source.total_us,
                });
                if let Some((reads, reused)) = source.checkout {
                    entry["checkout"] =
                        serde_json::json!({ "reads": reads, "reused_boundaries": reused });
                }
                entry
            }).collect::<Vec<_>>(),
            "landed": landed,
            "unread_work": crate::package_record::absent(UNREAD_WORK_ABSENT),
        });
        let mut bytes =
            trust_types::digest::canonical_json_bytes(&value).expect("a JSON value serializes");
        bytes.push(b'\n');
        String::from_utf8(bytes).expect("serde_json writes UTF-8")
    }

    fn render_terminal(&self, top: usize) -> String {
        let mut out = String::new();
        out.push_str(&format!("targo trust meter: read {} source(s)\n", self.sources.len()));
        let waited = self.waited();
        if waited.is_empty() {
            out.push_str("Waited: nothing measured\n");
        } else {
            let mut parts: Vec<(u64, String)> = waited
                .iter()
                .map(|(category, (us, partial))| {
                    (
                        *us,
                        format!(
                            "{category} {}{}",
                            duration(*us),
                            if *partial { " + untotalled" } else { "" }
                        ),
                    )
                })
                .collect();
            parts.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
            let parts: Vec<String> = parts.into_iter().map(|(_, text)| text).collect();
            out.push_str(&format!("Waited: {}\n", parts.join(" · ")));
        }
        out.push_str(&format!("No source read here records: {}\n", NOT_RECORDED.join(", ")));
        if !self.rows.is_empty() {
            let shown = if top == 0 { self.rows.len() } else { top.min(self.rows.len()) };
            let phase_width =
                self.rows[..shown].iter().map(|row| row.phase.len()).max().unwrap_or(5).max(5);
            let item_width = self.rows[..shown]
                .iter()
                .map(|row| row.item.chars().count())
                .max()
                .unwrap_or(4)
                .clamp(4, 48);
            out.push_str(&format!(
                "\n{:>9}  {:<phase_width$}  {:<item_width$}  SOURCE\n",
                "WAIT", "PHASE", "ITEM"
            ));
            for row in &self.rows[..shown] {
                let item = if row.count > 1 {
                    format!("{} (x{})", row.item, row.count)
                } else {
                    row.item.clone()
                };
                out.push_str(&format!(
                    "{:>9}  {:<phase_width$}  {:<item_width$}  {}\n",
                    duration(row.wait_us),
                    row.phase,
                    truncate(&item, item_width),
                    row.source
                ));
            }
            if shown < self.rows.len() {
                let rest: u64 = self.rows[shown..].iter().map(|row| row.wait_us).sum();
                out.push_str(&format!(
                    "… {} more row(s), {} in all; --top 0 prints every row\n",
                    self.rows.len() - shown,
                    duration(rest)
                ));
            }
        }
        out.push('\n');
        if self.landed.gate_runs == 0 {
            out.push_str("Landed: not derivable yet (no gate run record was read)\n");
        } else {
            let window = match (self.landed.from_unix_s, self.landed.to_unix_s) {
                (Some(from), Some(to)) => format!("{} .. {} UTC", utc(from), utc(to)),
                _ => "an unknown window".to_string(),
            };
            let unrecorded = match self.landed.runs_without_record {
                0 => String::new(),
                runs => format!(" ({runs} more run(s) left no record.json and are not counted)"),
            };
            out.push_str(&format!(
                "Landed through the gate: {} of {} gate run(s){unrecorded}, records written \
                 {window}; pushes made outside the gate are not in these records\n",
                self.landed.through_gate, self.landed.gate_runs
            ));
        }
        out.push_str(&format!(
            "Landed per agent-hour and per processor-hour: not derivable yet ({})\n",
            AGENT_HOURS_ABSENT.1
        ));
        out.push_str(&format!("Unread work: not derivable yet ({})\n", UNREAD_WORK_ABSENT.1));
        if !self.missing.is_empty() {
            out.push_str("\nNot measured:\n");
            // One line per (phase, reason): the items and sources it covers.
            let mut grouped: BTreeMap<(&str, &str), Vec<String>> = BTreeMap::new();
            for missing in &self.missing {
                grouped.entry((missing.phase.as_str(), missing.why.as_str())).or_default().push(
                    if missing.item == "-" {
                        missing.source.clone()
                    } else {
                        format!("{} ({})", missing.item, missing.source)
                    },
                );
            }
            for ((phase, why), items) in grouped {
                out.push_str(&format!("  {phase}: {why}: {}\n", items.join(", ")));
            }
        }
        out
    }
}

const AGENT_HOURS_ABSENT: (&str, &str) =
    ("PKG-LIVE-1", "no record holds the agent-hours or processor-hours behind a landed change");
const PROCESSOR_HOURS_ABSENT: (&str, &str) = AGENT_HOURS_ABSENT;
const UNREAD_WORK_ABSENT: (&str, &str) =
    ("PKG-LIVE-1", "no record says which computed results an agent read");

/// What several rows a gate leg ran, or `None` for a leg that is one check.
fn leg_rows(leg: &str, entry: &Value) -> Option<String> {
    if SINGLE_CHECK_LEGS.contains(&leg) {
        return None;
    }
    Some(match (leg, entry.get("targets").and_then(Value::as_array)) {
        // Which rows depends on the profile (those no other leg covers, or
        // every fresh one with `--all-rows`); the reason names neither.
        ("push-rows", _) => "it runs push-profile rows (`bash \
                             tests/run_trust_comprehensive_harness.sh --list push`), and its log \
                             has no per-row time"
            .to_string(),
        // `targets` is the leg's plan (`scripts/land_gate.py` writes it before
        // any cache lookup or narrowing), not a count of what ran; the
        // members a cached PASS answered for are `cached_members`.
        (_, Some(targets)) => {
            let planned: std::collections::BTreeSet<&str> =
                targets.iter().filter_map(Value::as_str).collect();
            let cached =
                entry.get("cached_members").and_then(Value::as_array).map_or(0, |cached| {
                    cached.iter().filter_map(Value::as_str).filter(|m| planned.contains(m)).count()
                });
            let cached = match cached {
                0 => String::new(),
                cached => format!(", {cached} of them answered by a cached PASS"),
            };
            format!("its plan names {} target(s){cached}, each one row or more", targets.len())
        }
        _ => "it is not a leg the meter knows to be one check (compiler-check, tidy, \
              tcb-panic-ratchet, ir-cohort, olean-audit), so it may run several rows"
            .to_string(),
    })
}

fn truncate(text: &str, width: usize) -> String {
    if text.chars().count() <= width {
        return text.to_string();
    }
    let kept: String = text.chars().take(width.saturating_sub(1)).collect();
    format!("{kept}…")
}

/// A wait for a person: `1h 02m`, `12m 05s`, `4.2 s`, `310 ms`, `85 us`.
fn duration(us: u64) -> String {
    let seconds = us / 1_000_000;
    if seconds >= 3600 {
        format!("{}h {:02}m", seconds / 3600, (seconds % 3600) / 60)
    } else if seconds >= 60 {
        format!("{}m {:02}s", seconds / 60, seconds % 60)
    } else if us >= 1_000_000 {
        format!("{:.1} s", us as f64 / 1_000_000.0)
    } else if us >= 1000 {
        format!("{} ms", us / 1000)
    } else {
        format!("{us} us")
    }
}

/// `YYYY-MM-DD HH:MM` in UTC (Howard Hinnant's days-to-civil).
fn utc(unix_s: u64) -> String {
    let days = i64::try_from(unix_s / 86_400).unwrap_or(i64::MAX / 2);
    let minute_of_day = (unix_s % 86_400) / 60;
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i64::from(month <= 2);
    format!("{year:04}-{month:02}-{day:02} {:02}:{:02}", minute_of_day / 60, minute_of_day % 60)
}

/// The fields of one pre-push `TIMING:` line, unquoted
/// (`scripts/hooks/pre-push` `timing_record`: `phase=… lane=%q elapsed_s=…
/// exit=… clock=… authority=… refs=%q`), or `None` for any other line.
fn parse_timing_line(line: &str) -> Option<BTreeMap<String, String>> {
    let start = line.find("TIMING: phase=")?;
    let rest = &line[start + "TIMING: ".len()..];
    let mut fields = BTreeMap::new();
    for token in split_shell_words(rest) {
        if let Some((key, value)) = token.split_once('=') {
            fields.insert(key.to_string(), value.to_string());
        }
    }
    fields.contains_key("phase").then_some(fields)
}

/// Split Bash `printf %q` output into words, removing its quoting: a
/// backslash escapes the next character, `'…'` is literal, and `$'…'` is
/// decoded as bytes, so a UTF-8 character `printf %q` wrote as octal bytes
/// reads back as that character.
fn split_shell_words(text: &str) -> Vec<String> {
    let mut words = Vec::new();
    let mut word = String::new();
    let mut in_word = false;
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            ' ' | '\t' => {
                if in_word {
                    words.push(std::mem::take(&mut word));
                    in_word = false;
                }
            }
            '\\' => {
                in_word = true;
                if let Some(next) = chars.next() {
                    word.push(next);
                }
            }
            '\'' => {
                in_word = true;
                for inner in chars.by_ref() {
                    if inner == '\'' {
                        break;
                    }
                    word.push(inner);
                }
            }
            '$' if chars.peek() == Some(&'\'') => {
                in_word = true;
                chars.next();
                word.push_str(&ansi_c_quoted(&mut chars));
            }
            other => {
                in_word = true;
                word.push(other);
            }
        }
    }
    if in_word {
        words.push(word);
    }
    words
}

/// The body of a Bash `$'…'` word, read after its opening quote through its
/// closing one, decoded as bytes ([`split_shell_words`]).
fn ansi_c_quoted(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> String {
    fn push(bytes: &mut Vec<u8>, c: char) {
        bytes.extend_from_slice(c.encode_utf8(&mut [0; 4]).as_bytes());
    }
    // Up to `max` more digits of `radix` onto `value`, and how many were read.
    fn more_digits(
        chars: &mut std::iter::Peekable<std::str::Chars<'_>>,
        radix: u32,
        max: usize,
        mut value: u32,
    ) -> (u32, usize) {
        let mut read = 0;
        while read < max {
            let Some(digit) = chars.peek().and_then(|c| c.to_digit(radix)) else { break };
            value = value * radix + digit;
            chars.next();
            read += 1;
        }
        (value, read)
    }
    let mut bytes = Vec::new();
    while let Some(c) = chars.next() {
        match c {
            '\'' => break,
            '\\' => match chars.next() {
                Some('a') => bytes.push(0x07),
                Some('b') => bytes.push(0x08),
                Some('e' | 'E') => bytes.push(0x1b),
                Some('f') => bytes.push(0x0c),
                Some('n') => bytes.push(b'\n'),
                Some('r') => bytes.push(b'\r'),
                Some('t') => bytes.push(b'\t'),
                Some('v') => bytes.push(0x0b),
                // At most three octal digits, one byte, as Bash reads them.
                Some(digit @ '0'..='7') => {
                    let (value, _) = more_digits(chars, 8, 2, digit.to_digit(8).unwrap_or(0));
                    bytes.push((value & 0xff) as u8);
                }
                Some('x') => match more_digits(chars, 16, 2, 0) {
                    (value, 1..) => bytes.push((value & 0xff) as u8),
                    _ => bytes.extend_from_slice(b"\\x"),
                },
                Some('c') => match chars.next() {
                    Some(control) => bytes.push((u32::from(control) & 0x1f) as u8),
                    None => bytes.extend_from_slice(b"\\c"),
                },
                Some(other @ ('\\' | '\'' | '"' | '?')) => push(&mut bytes, other),
                Some(other) => {
                    bytes.push(b'\\');
                    push(&mut bytes, other);
                }
                None => bytes.push(b'\\'),
            },
            other => push(&mut bytes, other),
        }
    }
    String::from_utf8_lossy(&bytes).into_owned()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn timing_lines_unquote_bash_printf_q() {
        let fields = parse_timing_line(
            "TIMING: phase=lane lane=fast.seed-freshness elapsed_s=12 exit=0 clock=bash-seconds \
             authority=none refs=refs/heads/main\\ 0123\\ refs/heads/main\\ 4567",
        )
        .expect("a TIMING line");
        assert_eq!(fields["phase"], "lane");
        assert_eq!(fields["lane"], "fast.seed-freshness");
        assert_eq!(fields["elapsed_s"], "12");
        assert_eq!(fields["refs"], "refs/heads/main 0123 refs/heads/main 4567");
        let fields =
            parse_timing_line("TIMING: phase=prepare lane=- elapsed_s=unavailable exit=- refs=''")
                .expect("a TIMING line");
        assert_eq!(fields["elapsed_s"], "unavailable");
        assert_eq!(fields["refs"], "");
        let fields = parse_timing_line("x TIMING: phase=lane lane=$'a\\tb' elapsed_s=1 exit=0")
            .expect("a TIMING line");
        assert_eq!(fields["lane"], "a\tb");
        assert!(parse_timing_line("PASS fast.seed-freshness").is_none());
    }

    /// `$'…'` decodes to bytes, so the octal bytes `printf %q` writes for a
    /// UTF-8 character read back as that character, and an escape the decoder
    /// does not know stays as written.
    #[test]
    fn ansi_c_quoting_decodes_bytes_not_latin_1() {
        let words = split_shell_words(
            "a=$'caf\\303\\251' b=$'\\xc3\\xa9' c=$'\\E[0m\\a\\v\\f\\b' d=$'\\cA\\0\\101x' \
             e=$'\\q\\?\\\"' f=$'\\x'",
        );
        assert_eq!(
            words,
            [
                "a=café",
                "b=é",
                "c=\u{1b}[0m\u{7}\u{b}\u{c}\u{8}",
                "d=\u{1}\u{0}Ax",
                "e=\\q?\"",
                "f=\\x",
            ]
        );
    }

    #[test]
    fn durations_and_dates_read_for_a_person() {
        assert_eq!(duration(85), "85 us");
        assert_eq!(duration(310_000), "310 ms");
        assert_eq!(duration(4_200_000), "4.2 s");
        assert_eq!(duration(725_000_000), "12m 05s");
        assert_eq!(duration(3_720_000_000), "1h 02m");
        assert_eq!(utc(0), "1970-01-01 00:00");
        assert_eq!(utc(1_794_571_200), "2026-11-13 12:00");
    }

    #[test]
    fn the_window_takes_hours_or_days_only() {
        assert_eq!(parse_window("12h"), Ok(Duration::from_secs(43_200)));
        assert_eq!(parse_window("2d"), Ok(Duration::from_secs(172_800)));
        for bad in ["", "h", "0h", "3", "3w", "-1h", "3\u{b5}"] {
            assert!(parse_window(bad).is_err(), "{bad}");
        }
    }
}
