//! `targo trust gate corpus-delta`: the command.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Duration;
use std::{env, fs};

use super::identity::{self, CompilerProbe, Identity, ProcessProbe};
use super::run::{self, CaseExit, CaseRunner, CaseSpec, CompilerProcess};
use super::table::{self, Corpus, TABLE, Table};
use super::{
    CaseRecord, Comparison, EXIT_COULD_NOT_RUN, EXIT_LOSS, EXIT_USAGE, RankFn, Verdict,
    compare_with, gate_args, rank,
};
use crate::durable_io;

const VERB: &str = "targo trust gate corpus-delta";

const USAGE: &str = "\
Usage: targo trust gate corpus-delta --old TRUSTC --new TRUSTC [--corpora LIST]
           [--keep DIR] [--fail-on-loss] [--case-seconds N] [--repo-root DIR]

Compile this checkout's daily-driver corpora once with each of two compilers and
print every case whose verdict moved against its pin.

The corpora are the rows of tests/corpora.toml (schema trust.corpora.v1): for
each, its case files, the compiler's arguments, and what each case is pinned to
(`verifies`, `refuses`, or nothing). A case's verdict is the compiler's own exit
status: `verifies` (0), `refuses` (1), or `crash:<status>` (anything else; a
compiler ended by a signal is 128 plus the signal). A verdict is ranked against
its pin: matching it is best, a crash is below a clean miss, and verifying a
case pinned `refuses` (a possible false proof) is worst. With no pin, `verifies`
is best.

  LOSS  a case whose rank fell, or one the old compiler had as pinned and the
        new compiler did not record
  GAIN  a case whose rank rose
  GONE  a case only the old compiler recorded, and not as pinned
  NEW   a case only the new compiler recorded

The old compiler runs over every corpus, then the new one, a case at a time.
Neither inherits TRUST_MEMORY_JOBSERVER_SOCK or TRUST_MEMORY_JOBSERVER, so
neither joins the host's trustd. A compiler is the path of a trustc: one is
never looked up on PATH or under build/. Each must answer `-vV`, and the report
names the commit each says it was built from.

Options:
  --old TRUSTC      The compiler the delta starts from
  --new TRUSTC      The compiler the delta ends at
  --corpora LIST    Comma-separated corpus ids (default: every corpus in the
                    table)
  --keep DIR        Keep the run in DIR, which must be empty or absent:
                    {old,new}/record.ndjson (schema trust.corpus-record.v1:
                    corpus, case, verdict, cause, pin), each compiler's `-vV`
                    output, every case's log, flips.txt and summary.txt. The
                    run names DIR by its resolved path (no `..`, no symlink)
  --fail-on-loss    Exit 1 when there is a LOSS
  --case-seconds N  A case with no verdict after N seconds is stopped and is
                    NOT JUDGED (default 1800). A side stops at its third such
                    case. A run with one compares nothing, and does not start
                    the new compiler when it was the old one's
  --repo-root DIR   The checkout whose table and corpora to use (default: the
                    nearest directory at or above the current one that holds
                    tests/corpora.toml)
  -h, --help        Show this help

Exit 0 when the report was printed, 1 with --fail-on-loss when there is a LOSS,
2 on a usage error (a compiler path that is no executable file and a --keep
directory in use are two) or a table that does not load, and 3 (COULD NOT RUN)
when a compiler does not answer `-vV`, a case cannot be started or is NOT
JUDGED, a corpus recorded no case, or the run's own files cannot be written.
2 outranks 3, and 3 outranks 1. Every run that has read its table and its
--corpora names the daily-driver corpora it did not compare, whatever its exit:
those the table has no row for yet, and those --corpora left out. A run refused
before that (on its arguments, on a table that does not load, or on a --corpora
list the table does not accept) names none. This compares exit statuses: it is
not a proof and grants nothing.
";

const DEFAULT_CASE_SECONDS: u64 = 1800;

/// A side stops at this many cases past their bound: a compiler that hangs on
/// every case would otherwise hold the run for the whole corpus's bounds.
const NOT_JUDGED_STOP: usize = 3;

const SIDES: [&str; 2] = ["old", "new"];

/// A side's record, in its directory.
const RECORD: &str = "record.ndjson";

struct Options {
    old: PathBuf,
    new: PathBuf,
    corpora: Option<String>,
    keep: Option<PathBuf>,
    fail_on_loss: bool,
    case_seconds: u64,
    repo_root: Option<PathBuf>,
}

fn parse(args: &[String]) -> Result<Option<Options>, String> {
    let Some(arguments) = gate_args::parse(
        args,
        &["--old", "--new", "--corpora", "--keep", "--case-seconds", "--repo-root"],
        &["--fail-on-loss"],
    )?
    else {
        return Ok(None);
    };
    let required = |name: &str| {
        arguments.value(name).map(PathBuf::from).ok_or_else(|| format!("{name} is required"))
    };
    let case_seconds = match arguments.value("--case-seconds") {
        None => DEFAULT_CASE_SECONDS,
        Some(text) => text.parse::<u64>().ok().filter(|seconds| *seconds > 0).ok_or_else(|| {
            format!("--case-seconds: {text:?} is not a number of seconds above 0")
        })?,
    };
    Ok(Some(Options {
        old: required("--old")?,
        new: required("--new")?,
        corpora: arguments.value("--corpora").map(str::to_owned),
        keep: arguments.value("--keep").map(PathBuf::from),
        fail_on_loss: arguments.flag("--fail-on-loss"),
        case_seconds,
        repo_root: arguments.value("--repo-root").map(PathBuf::from),
    }))
}

/// What the verb runs on: the caller's directory, the two things it asks of a
/// compiler, where progress goes, and the rank (the tests' mutant control
/// swaps it).
pub(crate) struct Host<'a> {
    pub(crate) cwd: PathBuf,
    pub(crate) runner: &'a mut dyn CaseRunner,
    pub(crate) probe: &'a mut dyn CompilerProbe,
    pub(crate) progress: &'a mut dyn FnMut(&str),
    pub(crate) rank: RankFn,
}

/// A run that ends before its report: the exit code and what to print.
struct Stop(u8, String);

impl Stop {
    fn usage(error: String) -> Self {
        Self(EXIT_USAGE, format!("{VERB}: {error}\n"))
    }

    fn could_not_run(why: &str) -> Self {
        Self(EXIT_COULD_NOT_RUN, could_not_run(why))
    }

    /// This stop, under the corpora the run was not going to compare. Every
    /// stop after the table and `--corpora` are read carries them: a refusal
    /// must not read as a run that covered the daily-driver corpora.
    fn naming(self, left_out: &str) -> Self {
        if left_out.is_empty() {
            return self;
        }
        Self(self.0, format!("{left_out}\n{}", self.1))
    }
}

fn could_not_run(why: &str) -> String {
    format!("CORPUS-DELTA: COULD NOT RUN — {why}\n")
}

fn absolute(cwd: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() { path.to_path_buf() } else { cwd.join(path) }
}

/// `--keep`'s directory, created, by its resolved path. A reused directory
/// would show the previous run's flips beside this run's counts, so it must be
/// empty.
///
/// The path is resolved because the run's records are written through
/// `durable_io`, which refuses a `..` component and a symlink its caller could
/// retarget. `--keep ../evidence` and a directory reached through the caller's
/// own symlink are ordinary requests, and unresolved they would be refused
/// only once the old compiler had compiled every case.
fn kept_dir(dir: &Path) -> Result<PathBuf, String> {
    match fs::read_dir(dir) {
        Ok(mut entries) => {
            if entries.next().is_some() {
                return Err(format!("--keep {} is not empty", dir.display()));
            }
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => fs::create_dir_all(dir)
            .map_err(|error| format!("cannot create --keep {}: {error}", dir.display()))?,
        Err(error) => return Err(format!("cannot read --keep {}: {error}", dir.display())),
    }
    fs::canonicalize(dir)
        .map_err(|error| format!("cannot resolve --keep {}: {error}", dir.display()))
}

/// The command and its tests use this one path.
pub(crate) fn run_with(args: &[String], host: &mut Host<'_>) -> (u8, String) {
    let options = match parse(args) {
        Ok(None) => return (0, USAGE.into()),
        Ok(Some(options)) => options,
        Err(error) => return (EXIT_USAGE, format!("{VERB}: {error}\n\n{USAGE}")),
    };
    match run_options(&options, host) {
        Ok(result) => result,
        Err(Stop(code, text)) => (code, text),
    }
}

fn run_options(options: &Options, host: &mut Host<'_>) -> Result<(u8, String), Stop> {
    // Everything that exits 2 is decided before anything that can exit 3.
    let root = match &options.repo_root {
        Some(dir) => absolute(&host.cwd, dir),
        None => host
            .cwd
            .ancestors()
            .find(|dir| dir.join(TABLE).is_file())
            .map(Path::to_path_buf)
            .ok_or_else(|| {
            Stop::usage(format!(
                "no {TABLE} in {} or above it; pass --repo-root",
                host.cwd.display()
            ))
        })?,
    };
    let table = table::load(&root)
        .map_err(|error| Stop::usage(format!("{}: {error}", root.join(TABLE).display())))?;
    let selected = table.select(options.corpora.as_deref()).map_err(Stop::usage)?;
    // From here every way out names what the run was not going to compare.
    let left_out = not_compared(&table, &selected);
    let compilers = [absolute(&host.cwd, &options.old), absolute(&host.cwd, &options.new)];
    for compiler in &compilers {
        if !identity::is_executable_file(compiler) {
            let error = format!("no executable compiler at {}", compiler.display());
            return Err(Stop::usage(error).naming(&left_out));
        }
    }
    let keep = match options.keep.as_deref() {
        None => None,
        Some(dir) => Some(
            kept_dir(&absolute(&host.cwd, dir))
                .map_err(|error| Stop::usage(error).naming(&left_out))?,
        ),
    };

    let cannot = |what: &str, error: std::io::Error| {
        Stop::could_not_run(&format!("cannot {what}: {error}")).naming(&left_out)
    };
    let scratch =
        tempfile::tempdir().map_err(|error| cannot("create a scratch directory", error))?;
    // Resolved for the reason `kept_dir` gives: `TMPDIR` is the caller's too.
    let scratch_dir = fs::canonicalize(scratch.path())
        .map_err(|error| cannot("resolve the scratch directory", error))?;
    let kept = keep.is_some();
    let out = keep.unwrap_or_else(|| scratch_dir.join("report"));
    let work = scratch_dir.join("work");
    SIDES
        .iter()
        .try_for_each(|side| {
            fs::create_dir_all(out.join(side))?;
            fs::create_dir_all(work.join(side))
        })
        .map_err(|error| cannot("create the run's directories", error))?;

    // A compiler that cannot report its own version would "refuse" every
    // case, so both answer before either compiles one.
    let mut identities: Vec<Identity> = Vec::new();
    for (side, compiler) in SIDES.iter().zip(&compilers) {
        let log = out.join(side).join("version.log");
        match identity::identify(&mut *host.probe, compiler, &log) {
            Ok(identity) => identities.push(identity),
            Err(why) => return Err(Stop::could_not_run(&why).naming(&left_out)),
        }
    }
    let head = host.probe.checkout_head(&root);
    let mut text = header(&selected, &left_out, &compilers, &identities, head.as_deref());

    // Both records exist, empty, before a case is compiled: a place the run
    // cannot write its records to is refused here, not after the old compiler
    // has compiled every case.
    for side in SIDES {
        let record = out.join(side).join(RECORD);
        if let Err(error) = durable_io::atomic_write_private(&record, b"") {
            text.push_str(&could_not_run(&format!(
                "{side}: cannot write {}: {error}",
                record.display()
            )));
            return Ok((EXIT_COULD_NOT_RUN, text));
        }
    }

    let bound = Duration::from_secs(options.case_seconds);
    let mut records: Vec<Vec<CaseRecord>> = Vec::new();
    for (side, compiler) in SIDES.iter().copied().zip(&compilers) {
        let run = Side { label: side, compiler, out: out.join(side), work: work.join(side), kept };
        let side_records = match run_side(&run, &selected, bound, host) {
            Ok(side_records) => side_records,
            Err(why) => {
                text.push_str(&could_not_run(&why));
                return Ok((EXIT_COULD_NOT_RUN, text));
            }
        };
        let unjudged: Vec<&CaseRecord> =
            side_records.iter().filter(|record| record.verdict == Verdict::NotJudged).collect();
        if !unjudged.is_empty() {
            for record in &unjudged {
                text.push_str(&format!(
                    "NOT JUDGED  {side} {}/{}: {}\n",
                    record.corpus, record.case, record.cause
                ));
            }
            text.push_str(&could_not_run(&format!(
                "the {side} compiler gave no verdict on {} case(s) within {}s each, so nothing \
                 was compared (--case-seconds raises the bound; a side stops at its case \
                 number {NOT_JUDGED_STOP} past it)",
                unjudged.len(),
                options.case_seconds
            )));
            return Ok((EXIT_COULD_NOT_RUN, text));
        }
        records.push(side_records);
    }

    let comparison = match compare_with(&records[0], &records[1], host.rank) {
        Ok(comparison) => comparison,
        Err(why) => {
            text.push_str(&could_not_run(&why));
            return Ok((EXIT_COULD_NOT_RUN, text));
        }
    };
    let flips: String = comparison.flip_lines().iter().map(|line| format!("{line}\n")).collect();
    let counts = summary(&comparison, &selected);
    let written = durable_io::atomic_write_private(&out.join("flips.txt"), flips.as_bytes())
        .and_then(|()| {
            durable_io::atomic_write_private(&out.join("summary.txt"), counts.as_bytes())
        });
    if let Err(error) = written {
        text.push_str(&could_not_run(&format!(
            "cannot write the report under {}: {error}",
            out.display()
        )));
        return Ok((EXIT_COULD_NOT_RUN, text));
    }
    text.push_str(&flips);
    if !flips.is_empty() {
        text.push('\n');
    }
    text.push_str(&counts);
    let code = if options.fail_on_loss && comparison.losses > 0 { EXIT_LOSS } else { 0 };
    Ok((code, text))
}

fn joined<'a>(ids: impl Iterator<Item = &'a str>) -> String {
    ids.collect::<Vec<_>>().join(", ")
}

/// The daily-driver corpora a run over `selected` does not compare, a line per
/// reason: those `--corpora` left out, and those the table has no row for yet.
/// Empty when there is none.
fn not_compared(table: &Table, selected: &[&Corpus]) -> String {
    let mut text = String::new();
    let unselected = joined(
        table
            .corpora
            .iter()
            .filter(|corpus| !selected.iter().any(|chosen| chosen.id == corpus.id))
            .map(|corpus| corpus.id.as_str()),
    );
    if !unselected.is_empty() {
        text.push_str(&format!("not compared: {unselected} (not named by --corpora)\n"));
    }
    if !table.not_on_yet.is_empty() {
        text.push_str(&format!(
            "not compared: {} (not in {TABLE} yet: {})\n",
            joined(table.not_on_yet.iter().map(|absent| absent.id.as_str())),
            joined(table.not_on_yet.iter().map(|absent| absent.script.as_str())),
        ));
    }
    text
}

/// Who was compared, over what, and what was left out.
fn header(
    selected: &[&Corpus],
    left_out: &str,
    compilers: &[PathBuf; 2],
    identities: &[Identity],
    head: Option<&str>,
) -> String {
    let mut text = String::new();
    for ((side, compiler), identity) in SIDES.iter().zip(compilers).zip(identities) {
        text.push_str(&format!("{side}: {}\n     {}\n", identity.headline(), compiler.display()));
        if let Some(note) = identity.note(side, head) {
            text.push_str(&format!("     {note}\n"));
        }
    }
    text.push_str(&format!(
        "corpora: {} (this checkout, {})\n",
        joined(selected.iter().map(|corpus| corpus.id.as_str())),
        head.map_or_else(|| "unknown".to_owned(), |head| head.chars().take(10).collect())
    ));
    text.push_str(left_out);
    text.push('\n');
    text
}

/// The counts under the flips.
fn summary(comparison: &Comparison, selected: &[&Corpus]) -> String {
    let mut text = format!("{:<10} {:>14} {:>14}\n", "corpus", "old as pinned", "new as pinned");
    for corpus in selected {
        let tally = comparison.tallies.get(&corpus.id).copied().unwrap_or_default();
        let row = format!(
            "{:<10} {:>8} / {:<4} {:>8} / {:<4}",
            corpus.id, tally.old_as_pinned, tally.old_total, tally.new_as_pinned, tally.new_total
        );
        text.push_str(row.trim_end());
        text.push('\n');
    }
    text.push_str(
        "(as pinned: the verdict the case is pinned to; verifies where nothing is pinned)\n",
    );
    if comparison.crashes > 0 {
        text.push_str(&format!("the new compiler crashed on {} case(s)\n", comparison.crashes));
    }
    text.push_str(&format!(
        "\nseal corpus delta: {} lost, {} gained\n",
        comparison.losses, comparison.gains
    ));
    text
}

/// One compiler's half of the run.
struct Side<'a> {
    label: &'a str,
    compiler: &'a Path,
    /// Its record and logs.
    out: PathBuf,
    /// Scratch for what the compiler writes.
    work: PathBuf,
    /// Whether `out` outlives the run (`--keep`).
    kept: bool,
}

/// Compile every selected corpus with one compiler and write the side's
/// record, whether or not the side finished.
fn run_side(
    side: &Side<'_>,
    corpora: &[&Corpus],
    bound: Duration,
    host: &mut Host<'_>,
) -> Result<Vec<CaseRecord>, String> {
    let label = side.label;
    let mut records = Vec::new();
    let finished = collect(side, corpora, bound, host, &mut records);
    let mut lines = String::new();
    for record in &records {
        let line = serde_json::to_string(record)
            .map_err(|error| format!("{label}: cannot write a record: {error}"))?;
        lines.push_str(&line);
        lines.push('\n');
    }
    let path = side.out.join(RECORD);
    durable_io::atomic_write_private(&path, lines.as_bytes())
        .map_err(|error| format!("{label}: cannot write {}: {error}", path.display()))?;
    finished.map(|()| records)
}

fn collect(
    side: &Side<'_>,
    corpora: &[&Corpus],
    bound: Duration,
    host: &mut Host<'_>,
    records: &mut Vec<CaseRecord>,
) -> Result<(), String> {
    let label = side.label;
    let create = |dir: &Path| {
        fs::create_dir_all(dir)
            .map_err(|error| format!("{label}: cannot create {}: {error}", dir.display()))
    };
    let mut unjudged = 0;
    for corpus in corpora {
        (host.progress)(&format!(
            "corpus-delta: {label}: {} ({} case(s))",
            corpus.id,
            corpus.cases.len()
        ));
        let work = side.work.join(&corpus.id);
        create(&work)?;
        let recorded_before = records.len();
        for case in &corpus.cases {
            let log = side.out.join(&corpus.id).join(format!("{}.log", case.id));
            if let Some(parent) = log.parent() {
                create(parent)?;
            }
            let spec = CaseSpec {
                compiler: side.compiler.to_path_buf(),
                corpus: corpus.id.clone(),
                case: case.id.clone(),
                args: case.args.clone(),
                source: case.source.clone(),
                work: work.clone(),
                log: log.clone(),
                bound,
            };
            let verdict = match host.runner.run(&spec) {
                Some(CaseExit::Exited(code)) => Verdict::of_exit(code),
                Some(CaseExit::Signalled(signal)) => Verdict::Crash(128 + signal),
                Some(CaseExit::PastBound) => Verdict::NotJudged,
                Some(CaseExit::Failed(error)) => {
                    return Err(format!("{label}: {}/{}: {error}", spec.corpus, spec.case));
                }
                None => continue,
            };
            let cause = match verdict {
                Verdict::Verifies => String::new(),
                // Without `--keep` the log goes with the run's scratch, so the
                // line names how to hold it, not a path that is gone.
                Verdict::NotJudged if side.kept => {
                    format!("no verdict within {}s (log: {})", bound.as_secs(), log.display())
                }
                Verdict::NotJudged => {
                    format!("no verdict within {}s (--keep DIR holds its log)", bound.as_secs())
                }
                Verdict::Refuses | Verdict::Crash(_) => run::first_error_line(&log),
            };
            records.push(CaseRecord {
                corpus: spec.corpus,
                case: spec.case,
                verdict,
                cause,
                pin: case.pin,
            });
            if verdict == Verdict::NotJudged {
                unjudged += 1;
                if unjudged == NOT_JUDGED_STOP {
                    return Ok(());
                }
            }
        }
        if records.len() == recorded_before {
            return Err(format!("{label}: corpus {} recorded no case", corpus.id));
        }
    }
    Ok(())
}

pub(crate) fn run_to_string(args: &[String]) -> (u8, String) {
    let cwd = match env::current_dir() {
        Ok(cwd) => cwd,
        Err(error) => {
            return (
                EXIT_COULD_NOT_RUN,
                could_not_run(&format!("cannot read the current directory: {error}")),
            );
        }
    };
    let mut progress = |line: &str| eprintln!("{line}");
    run_with(
        args,
        &mut Host {
            cwd,
            runner: &mut CompilerProcess,
            probe: &mut ProcessProbe,
            progress: &mut progress,
            rank,
        },
    )
}

pub(crate) fn run_subcommand(args: &[String]) -> ExitCode {
    let (code, text) = run_to_string(args);
    if code == 0 || code == EXIT_LOSS {
        print!("{text}");
    } else {
        eprint!("{text}");
    }
    ExitCode::from(code)
}
