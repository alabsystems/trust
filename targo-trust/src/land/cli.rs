//! `targo trust land --check`: the command.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Duration;
use std::{env, fs};

use super::run::{self, RowProcess, RowRunner, RowSpec, Verdict};
use super::select::{self, Change, Checkout, GitCheckout, MANIFEST_ROW};
use super::table::{self, NotRunKind, TABLE, Table};
use super::{EXIT_COULD_NOT_RUN, EXIT_FAIL, EXIT_USAGE};
use crate::gate_args;

const VERB: &str = "targo trust land";

const USAGE: &str = "\
Usage: targo trust land --check [--base REV] [--repo-root DIR] [--row-seconds N]

Run the validation rows of gates/land.toml that a change selects, and print one
verdict per row. Validation rows only; this is not the landing gate: the gate is
`python3 scripts/land_gate.py run`, which still selects and runs these rows
itself, and runs every other leg. No gate calls this verb yet. Without --check,
`targo trust land` is the landing, which is not implemented in Targo yet: it
exits 2.

The table (schema trust.land-rows.v1) is read as scripts/lib/land_select.py
reads it and refused whole where that reader refuses it: another schema, an
unknown or missing key, ids that are not sorted and unique, a command that is
not the row's validation runner, an empty selects_on, catches or not_yet_targo,
a [validation_programs] entry that is not exactly the rows whose selects_on
names its path, or a table that is not a regular file in a real directory. A
tracked file the table's `covered` globs match must be exactly one [[row]] or
exactly one [[not_run]], and each of those must name a tracked file. A row
whose command does not start `targo` must say why in `not_yet_targo`.

The change is every path that differs between HEAD and its merge base with
--base, and every path that is staged, changed in the working tree, or
untracked. (The Python gate judges a commit; this judges the checkout as it
stands.) Git reports no change to a path whose index entry is marked
assume-unchanged or skip-worktree, so a checkout with such an entry is exit 3
and never a smaller change. A row is selected when the change names one of its
`selects_on` paths.
A change to the table selects the rows of scripts/lib/land_select.py, and any
changed Cargo.toml selects validation.mir_test_oracle_feature_test.

Each selected row's command runs from the checkout's root, with no stdin and
its output in a log, for at most --row-seconds:

  PASS        the command exited 0
  FAIL        it exited with any other status but 2, or a signal ended it
  NOT JUDGED  it exited 2 (the runner's \"no test ran\"), it was still running
              at its bound (the line carries the command to rerun), it could
              not be started, or the table has no row of the selected id

Every --check run ends with the line
\"validation rows only; this is not the landing gate\", but two: one whose
arguments are refused ends with this help, which holds that line's words, and
one a signal stops ends with that signal's COULD NOT RUN line. A run that has
loaded its table prints before that line \"N of M rows are not yet a targo verb
or test target\", the count of [[not_run]] rows by kind, and what this verb
does not judge. Once it has read the change it prints, before those, the base
and how many paths changed, and each selected row and its verdict.

Not judged by this verb: the rows the Python gate adds when incoming main
changes the table while a landing is composed (its owner refresh), the tests
`land_gate.py plan --development` takes from scripts/lib/land_development.py,
and every leg of the gate but validation-tests.

Options:
  --check           Select and run the validation rows (required)
  --base REV        The commit the change is measured from, through its merge
                    base with HEAD (default: origin/main). A base that does not
                    resolve is exit 3, never an empty change
  --repo-root DIR   The checkout whose table to use (default: the nearest
                    directory at or above the current one that holds
                    gates/land.toml)
  --row-seconds N   How long one row's command may take (default 900). A row
                    past it is NOT JUDGED, never a PASS. No row carries a bound
                    of its own, so a change that selects a row slower than N
                    needs a larger N; an N past the end of the clock is no
                    bound
  -h, --help        Show this help

Exit 0 when every selected row passed, or when no row was selected (the report
says so and why); 1 when a row FAILed; 2 on a usage error, a table that does
not load, or a tree that breaks the table's `covered` rule; and 3 (COULD NOT
RUN) when the base does not resolve, git fails, the index hides a path from
git, a log cannot be written, a row is NOT JUDGED, or a signal stops the run.
2 outranks 3, and 3 outranks 1; the `covered` rule needs git's list of tracked
files, so git failing to list them is 3. The report is on stdout at exit 0 and
1 and on stderr at exit 2 and 3; one line per row started is on stderr.
";

/// The verb's line in `targo trust --help` (`cli::usage_text`). It is here,
/// beside the handler it describes.
pub(crate) const USAGE_LINE: &str = "  targo trust land --check [--base <rev>]  Run the validation \
     rows of gates/land.toml that a change selects, one verdict per row; validation rows only, \
     not the landing gate";

const DEFAULT_BASE: &str = "origin/main";
const DEFAULT_ROW_SECONDS: u64 = 900;

const NOT_JUDGED_HERE: &str = "not judged here: the rows the Python gate adds when incoming main \
     changes gates/land.toml (its owner refresh), the tests of `land_gate.py plan \
     --development` (scripts/lib/land_development.py), and every leg but validation-tests";
const FOOTER: &str = "validation rows only; this is not the landing gate";

struct Options {
    base: String,
    row_seconds: u64,
    repo_root: Option<PathBuf>,
}

enum Request {
    Help,
    /// `targo trust land` without `--check`: the landing itself.
    Landing,
    Check(Options),
}

fn parse(args: &[String]) -> Result<Request, String> {
    let Some(arguments) =
        gate_args::parse(args, &["--base", "--repo-root", "--row-seconds"], &["--check"])?
    else {
        return Ok(Request::Help);
    };
    if !arguments.flag("--check") {
        return Ok(Request::Landing);
    }
    let row_seconds = match arguments.value("--row-seconds") {
        None => DEFAULT_ROW_SECONDS,
        Some(text) => {
            text.parse::<u64>().ok().filter(|seconds| *seconds > 0).ok_or_else(|| {
                format!("--row-seconds: {text:?} is not a number of seconds above 0")
            })?
        }
    };
    Ok(Request::Check(Options {
        base: arguments.value("--base").unwrap_or(DEFAULT_BASE).to_owned(),
        row_seconds,
        repo_root: arguments.value("--repo-root").map(PathBuf::from),
    }))
}

/// What the verb runs on: the caller's directory, the checkout's answers, what
/// runs a row, and where progress goes.
pub(crate) struct Host<'a> {
    pub(crate) cwd: PathBuf,
    pub(crate) checkout: &'a mut dyn Checkout,
    pub(crate) runner: &'a mut dyn RowRunner,
    pub(crate) progress: &'a mut dyn FnMut(&str),
}

/// A run that ends before its report: the exit code and what to print.
struct Stop(u8, String);

impl Stop {
    /// A checkout or a table the verb cannot use. No table loaded, so there
    /// are no rows to count; the run still says what it is.
    fn usage(error: &str) -> Self {
        Self(EXIT_USAGE, format!("{VERB}: {error}\n{FOOTER}\n"))
    }

    /// COULD NOT RUN, over what every run of a loaded table says.
    fn could_not_run(why: &str, table: &Table) -> Self {
        Self(EXIT_COULD_NOT_RUN, format!("{}{}", could_not_run(why), trailer(table)))
    }
}

fn could_not_run(why: &str) -> String {
    format!("LAND-CHECK: COULD NOT RUN — {why}\n")
}

fn absolute(cwd: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() { path.to_path_buf() } else { cwd.join(path) }
}

/// What every run of a loaded table ends with.
fn trailer(table: &Table) -> String {
    let not_targo = table.rows.iter().filter(|row| !row.is_targo()).count();
    let kinds: Vec<String> = NotRunKind::ALL
        .iter()
        .map(|kind| {
            let count = table.not_run.iter().filter(|entry| entry.kind == *kind).count();
            format!("{count} {}", kind.word())
        })
        .collect();
    format!(
        "{not_targo} of {} rows are not yet a targo verb or test target\n\
         not run: {} [[not_run]] row(s): {}\n\
         {NOT_JUDGED_HERE}\n\
         {FOOTER}\n",
        table.rows.len(),
        table.not_run.len(),
        kinds.join(", ")
    )
}

fn short(commit: &str) -> &str {
    commit.get(..12).unwrap_or(commit)
}

/// The base, and how much changed.
fn header(base: &str, change: &Change, changed: usize) -> String {
    format!(
        "land --check: base {base} ({}), merge base {}, HEAD {}\n\
         changed: {changed} path(s) ({} between the merge base and HEAD, {} staged, changed in \
         the working tree or untracked)\n",
        short(&change.base),
        short(&change.merge_base),
        short(&change.head),
        change.committed.len(),
        change.working.len()
    )
}

/// The command and its tests use this one path.
pub(crate) fn run_with(args: &[String], host: &mut Host<'_>) -> (u8, String) {
    let options = match parse(args) {
        Ok(Request::Help) => return (0, USAGE.into()),
        Ok(Request::Landing) => {
            return (
                EXIT_USAGE,
                format!(
                    "{VERB}: the landing is not implemented in Targo yet (docs/PLAN.md \
                     PKG-LIVE-4). Land with `python3 scripts/land_gate.py run` and an ordinary \
                     push; `{VERB} --check` runs the validation rows a change selects.\n\n{USAGE}"
                ),
            );
        }
        Ok(Request::Check(options)) => options,
        Err(error) => return (EXIT_USAGE, format!("{VERB}: {error}\n\n{USAGE}")),
    };
    match run_options(&options, host) {
        Ok(result) => result,
        Err(Stop(code, text)) => (code, text),
    }
}

fn run_options(options: &Options, host: &mut Host<'_>) -> Result<(u8, String), Stop> {
    // Everything that exits 2 is decided before anything that can exit 3,
    // but for the `covered` rule, which needs git's list of tracked files.
    let root = match &options.repo_root {
        Some(dir) => absolute(&host.cwd, dir),
        None => host
            .cwd
            .ancestors()
            .find(|dir| dir.join(TABLE).is_file())
            .map(Path::to_path_buf)
            .ok_or_else(|| {
            Stop::usage(&format!(
                "no {TABLE} in {} or above it; pass --repo-root",
                host.cwd.display()
            ))
        })?,
    };
    let root = fs::canonicalize(&root)
        .map_err(|error| Stop::usage(&format!("no checkout at {}: {error}", root.display())))?;
    let table = table::load(&root).map_err(|error| Stop::usage(&format!("{TABLE}: {error}")))?;
    let tracked = host
        .checkout
        .tracked(&root)
        .map_err(|error| Stop::could_not_run(&format!("the tracked files: {error}"), &table))?;
    let problems = table.coverage(&tracked);
    if !problems.is_empty() {
        // The table loaded, so this refusal ends as every run of one does.
        return Err(Stop(
            EXIT_USAGE,
            format!(
                "{VERB}: {TABLE}: {} file(s) break its `covered` rule (each covered file is \
                 exactly one [[row]] or exactly one [[not_run]], and each of those names a \
                 tracked file):\n  {}\n{}",
                problems.len(),
                problems.join("\n  "),
                trailer(&table)
            ),
        ));
    }

    let change = host
        .checkout
        .change(&root, &options.base)
        .map_err(|error| Stop::could_not_run(&error, &table))?;
    let changed = change.paths();
    let ids = select::selected(&table, &changed);
    let mut text = header(&options.base, &change, changed.len());
    text.push_str(&format!("selected: {} of {} rows", ids.len(), table.rows.len()));
    if ids.is_empty() {
        text.push_str(if changed.is_empty() {
            ": nothing changed\n"
        } else {
            ": no changed path is a row's selects_on path, the table, or a Cargo.toml\n"
        });
        text.push_str(&trailer(&table));
        return Ok((0, text));
    }
    text.push('\n');

    let logs = tempfile::Builder::new()
        .prefix("targo-trust-land-")
        .tempdir()
        .and_then(|logs| Ok((fs::canonicalize(logs.path())?, logs)));
    let (logs_dir, logs) = match logs {
        Ok(logs) => logs,
        Err(error) => {
            text.push_str(&could_not_run(&format!("cannot create a directory for logs: {error}")));
            text.push_str(&trailer(&table));
            return Ok((EXIT_COULD_NOT_RUN, text));
        }
    };
    let bound = Duration::from_secs(options.row_seconds);
    let (mut passed, mut failed, mut unjudged) = (0usize, 0usize, 0usize);
    let mut logged = false;
    for (position, id) in ids.iter().enumerate() {
        let verdict = match table.row(id) {
            Some(row) => {
                let spec = RowSpec {
                    id: id.clone(),
                    argv: row.command.clone(),
                    root: root.clone(),
                    log: run::log_path(&logs_dir, id),
                    bound,
                };
                (host.progress)(&format!(
                    "land --check: {id} ({} of {}), at most {}s: {}",
                    position + 1,
                    ids.len(),
                    options.row_seconds,
                    run::command_line(&spec.argv)
                ));
                logged = true;
                run::judge(&spec, &host.runner.run(&spec))
            }
            // Only the manifest rule names a row without finding it.
            None => Verdict::NotJudged(format!(
                "selected, and {TABLE} has no [[row]] of that id{}",
                if id == MANIFEST_ROW { " (a changed Cargo.toml selects it)" } else { "" }
            )),
        };
        let word = verdict.word();
        match &verdict {
            Verdict::Pass => {
                passed += 1;
                text.push_str(&format!("{word:<11} {id}\n"));
            }
            Verdict::Fail(why) => {
                failed += 1;
                text.push_str(&format!("{word:<11} {id}: {why}\n"));
            }
            Verdict::NotJudged(why) => {
                unjudged += 1;
                text.push_str(&format!("{word:<11} {id}: {why}\n"));
            }
        }
    }
    text.push_str(&format!(
        "land --check: {passed} PASS, {failed} FAIL, {unjudged} NOT JUDGED of {} selected \
         row(s)\n",
        ids.len()
    ));
    if logged && failed + unjudged > 0 {
        // The lines above name logs: they outlive the run.
        let _ = logs.keep();
    }
    let code = if unjudged > 0 {
        text.push_str(&could_not_run(&format!(
            "{unjudged} selected row(s) had no verdict, so the change is not judged"
        )));
        EXIT_COULD_NOT_RUN
    } else if failed > 0 {
        EXIT_FAIL
    } else {
        0
    };
    text.push_str(&trailer(&table));
    Ok((code, text))
}

pub(crate) fn run_to_string(args: &[String]) -> (u8, String) {
    let cwd = match env::current_dir() {
        Ok(cwd) => cwd,
        Err(error) => {
            return (
                EXIT_COULD_NOT_RUN,
                format!(
                    "{}{FOOTER}\n",
                    could_not_run(&format!("cannot read the current directory: {error}"))
                ),
            );
        }
    };
    let mut progress = |line: &str| eprintln!("{line}");
    run_with(
        args,
        &mut Host {
            cwd,
            checkout: &mut GitCheckout,
            runner: &mut RowProcess,
            progress: &mut progress,
        },
    )
}

pub(crate) fn run_subcommand(args: &[String]) -> ExitCode {
    let (code, text) = run_to_string(args);
    if code == 0 || code == EXIT_FAIL {
        print!("{text}");
    } else {
        eprint!("{text}");
    }
    ExitCode::from(code)
}
