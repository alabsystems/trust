//! `targo trust stability`: the determinism instrument (work item T4.7; plan
//! `docs/design/2026-09-29-incremental-deterministic-trust-results.md` §3.8).
//!
//! The claim it tests is per unit: the same inputs give the same verdict
//! vector. The verb runs the crate-mode `targo trust check` its arguments
//! describe as LEGS — each a fresh `check` process with a fresh target
//! directory — under a pair of conditions per AXIS that must not matter, and
//! compares, per package, the verdict-vector digest that run's
//! `trust.package.v1` record states (T7c; the digest is T9's, over the stable
//! obligation keys). The records `targo trust check` writes are the one source:
//! the verb keeps no second account of a run. Where two digests differ, the
//! obligation records (`trust.obligations.v1`) name the keys whose status or
//! stop moved.
//!
//! AXES (each a pair of legs):
//!
//! * `repetition`: `base` / `repeat`, the same command twice.
//! * `parallelism`: `base` / `serial`, `CARGO_BUILD_JOBS=1` and
//!   `--worker-threads 1` against the defaults (the job count Cargo's
//!   configuration gives the checkout, an inherited `CARGO_BUILD_JOBS`
//!   removed). The serial leg's records must state `worker_threads` 1, so the
//!   axis cannot pass on a flag that never reached the run (what the compiler
//!   then did with it, it does not echo).
//! * `path`: `base` / `moved`, the workspace copied to another absolute path
//!   with every package directory its resolve reads by path, each at its
//!   position below their common root (`closure::PathClosure`), so the copy
//!   is a second checkout of the same tree. The copy must read the same Cargo
//!   configuration above that root as the caller's checkout
//!   (`legs::ancestor_cargo_configs`), or the axis would also compare that
//!   configuration: could-not-run, naming the files.
//! * `version`: `moved` / `bumped`, that copy again with the patch component
//!   of every recorded package's version bumped (its own, or the workspace's
//!   it inherits) and its `Cargo.lock` entry with it, and nothing else
//!   changed; a package whose version could not be moved makes the `bumped`
//!   leg could-not-run.
//! * `load`: `base` / `loaded`, idle against `2 x cores` busy loops (at most
//!   256): a load generator the verb owns from its spawn and stops through the
//!   one stop path (`crate::process_lifecycle`), never left running.
//! * `effort` (not in §3.8's table; only when asked for): `effort` /
//!   `effort-loaded`, a copy whose root `[trust]` table says `effort = 1`, idle
//!   against loaded; the count must actually stop something (a row or the
//!   ledger states `effort`), so the axis cannot pass vacuously. Until
//!   KNOWN_HAZARDS BUDGET-1 closes nothing does, and the axis fails.
//! * `host`: `base` / another host's records (`--against`). The other host runs
//!   `targo trust check` by hand with the same arguments and toolchain, and its
//!   `<target>/trust` directory (both records of every package) is carried
//!   here; the verb does not fake a second host. Both records must name the
//!   same targo-trust commit, and a build that names none is refused: the
//!   records name no toolchain (no seal until A8), so that commit is the only
//!   word that both hosts ran one.
//!
//! NEGATIVE CONTROL. Every run also checks a copy whose root `[trust]` table
//! says `backstop = 1` (5 ms per query): at least one package must come out not
//! measured with a `wall-backstop` stop (§3.8). An instrument that reads a
//! clock-decided run as a measurement proves nothing by agreeing with itself.
//!
//! VERDICTS, per axis and package: `equal` (both legs measured — `measured`,
//! coverage complete, every stop deterministic, no def path published with
//! two source digests — under the same profile to the same vector; the key
//! count is stated), `differing` (both measured, and the profile or the vector
//! differs: the moved keys are named), `not-reproducible` (a record states a
//! defect plan §2 says to fix at its producer: a solver fault or an
//! unexplained stop, or an outcome no stated stop explains), `could-not-run`
//! (a leg did not run, wrote no record of the package, its record is not a
//! measurement for a host's limit — it could not run, its coverage is
//! incomplete, only a backstop fired, two functions share a def path — or the
//! legs read different Cargo configuration). Neither of the last two passes an
//! axis; a verdict that compares nothing still carries both records' vectors
//! and profiles where both exist.
//!
//! EXIT: 0 every requested axis equal for every package it covers, and the
//! control caught; 1 an axis differs, a record is not reproducible, or an
//! instrument check failed (a package of the control ran and none read not
//! measured with a `wall-backstop` stop, the serial leg did not state one
//! worker thread, the effort axis stopped nothing on its count); 2 usage, or an
//! `--against` record of another lane, policy, selection, targo-trust commit or
//! budget profile than this host's run, or of a build that names no commit
//! (compare like with like); 3 otherwise, when a leg could not run or no
//! package of the control ran.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

mod closure;
mod judge;
mod legs;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

pub(crate) use judge::{AxisResult, ControlResult, Side, UnitFacts};
pub(crate) use legs::{CheckProcess, LegRunner};

/// The schema name of the verb's JSON output.
pub(crate) const STABILITY_SCHEMA: &str = "trust.stability.v1";

/// Exit: every requested axis equal and the control caught.
pub(crate) const EXIT_EQUAL: u8 = 0;
/// Exit: an axis differs, a record is not reproducible, or an instrument check
/// failed.
pub(crate) const EXIT_DIFFERING: u8 = 1;
/// Exit: usage, or an `--against` record not comparable with this host's run.
pub(crate) const EXIT_USAGE: u8 = 2;
/// Exit: a leg could not run (`determinism_report::EXIT_COULD_NOT_RUN`).
pub(crate) const EXIT_COULD_NOT_RUN: u8 = crate::determinism_report::EXIT_COULD_NOT_RUN;

const USAGE: &str = "\
Usage: targo trust stability [--axes <axis>[,<axis>...]] [--against <dir>]
                             [--scratch <dir>] [--keep] [--format terminal|json]
                             [check options]

Run the crate-mode `targo trust check` the check options describe as legs, each a
fresh process with its own target directory, under a pair of conditions per axis,
and compare each package's verdict-vector digest from the legs' trust.package.v1
records. Where two digests differ, the trust.obligations.v1 records name the keys.

Axes (default: repetition, parallelism, path, version and load; host as well
when --against is given):
  repetition   the same command twice
  parallelism  CARGO_BUILD_JOBS=1 and --worker-threads 1, against the defaults
  path         the workspace copied to another absolute path, with every
               package directory it reads by path at the same place relative
               to it; the copy must read the same Cargo configuration above
               it as the original
  version      that copy with each recorded package's version patch bumped
               (its own or its workspace's) and its Cargo.lock entry with it
  load         idle, against 2 x cores busy loops (at most 256) the verb owns
  effort       [trust] effort = 1, idle against loaded; something must stop on
               it. Only when asked for: until KNOWN_HAZARDS BUDGET-1 closes,
               nothing stops on effort and this axis fails
  host         this host against another host's records (--against)
Every run also checks a negative control, a copy with [trust] backstop = 1: at
least one package must read not measured with a wall-backstop stop.

Options:
  --axes <list>       Comma-separated axes to run
  --against <dir>     Another host's records: a directory holding the trust/
                      directory `targo trust check` wrote into its target
                      directory there (trust/packages/<package>.json and
                      trust/obligations/<package>.ndjson); its packages are
                      compared
  --scratch <dir>     Where the legs' copies, target directories and logs go
                      (default: $TMPDIR, else $HOME), in a private
                      trust-stability.* directory removed at the end
  --keep              Keep that directory, and every leg's target directory
  --format <fmt>      terminal (default) or json (`trust.stability.v1`); --json
                      is the same as --format json

Run it from the package's directory. Every other option goes to each leg's
check: lane flags, -p/--workspace, target and feature selection. Refused, because
the verb owns them or a leg could not honour them: --manifest-path, --target-dir,
--worker-threads, -j/--jobs, a --config that sets build.jobs or build.target-dir,
--report-dir, --save-baseline, --baseline, --rewrite, --standalone, and a
single-file operand; a --scratch inside the copy's root (the nearest directory
that holds the workspace and everything it reads by path); and a path
dependency written as an absolute path, which no copy could move.

Exit status:
  0  every requested axis equal for every package it covers; the control caught
  1  an axis differs; a record is not reproducible (it states a solver fault
     or an unexplained stop, a defect to fix where it is produced); or an
     instrument check failed (a package of the control ran and none read not
     measured with a wall-backstop stop, the serial leg did not record one
     worker thread, nothing stopped on effort at the smallest scale)
  2  usage, or an --against record of another lane, policy, selection,
     targo-trust commit or budget profile than this host's run, or of a build
     that names no targo-trust commit
  3  otherwise, a leg could not run: no record, or one that is no measurement
     for a host's limit (outcome could-not-run, coverage incomplete, only a
     backstop fired, a def path published with two source digests), or legs
     that read different Cargo configuration; or no package of the control ran
     to a complete coverage. could-not-run passes no axis
";

/// An axis: a pair of conditions that must not change any verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Axis {
    Repetition,
    Parallelism,
    Path,
    Version,
    Load,
    Effort,
    Host,
}

impl Axis {
    /// Every axis, in report order.
    pub(crate) const ALL: [Axis; 7] = [
        Axis::Repetition,
        Axis::Parallelism,
        Axis::Path,
        Axis::Version,
        Axis::Load,
        Axis::Effort,
        Axis::Host,
    ];

    pub(crate) fn name(self) -> &'static str {
        match self {
            Axis::Repetition => "repetition",
            Axis::Parallelism => "parallelism",
            Axis::Path => "path",
            Axis::Version => "version",
            Axis::Load => "load",
            Axis::Effort => "effort",
            Axis::Host => "host",
        }
    }

    pub(crate) fn parse(name: &str) -> Option<Axis> {
        Axis::ALL.into_iter().find(|axis| axis.name() == name)
    }

    /// The two legs the axis compares; `None` on the right for `host`, whose
    /// right side is another host's record.
    pub(crate) fn legs(self) -> (Leg, Option<Leg>) {
        match self {
            Axis::Repetition => (Leg::Base, Some(Leg::Repeat)),
            Axis::Parallelism => (Leg::Base, Some(Leg::Serial)),
            Axis::Path => (Leg::Base, Some(Leg::Moved)),
            Axis::Version => (Leg::Moved, Some(Leg::Bumped)),
            Axis::Load => (Leg::Base, Some(Leg::Loaded)),
            Axis::Effort => (Leg::Effort, Some(Leg::EffortLoaded)),
            Axis::Host => (Leg::Base, None),
        }
    }
}

/// One `targo trust check` run of the verb. Declared in run order: the
/// negative control first, so an instrument that cannot see a clock is named
/// before anything else is spent.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Leg {
    Control,
    Base,
    Repeat,
    Serial,
    Moved,
    Bumped,
    Loaded,
    Effort,
    EffortLoaded,
}

impl Leg {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Leg::Control => "control",
            Leg::Base => "base",
            Leg::Repeat => "repeat",
            Leg::Serial => "serial",
            Leg::Moved => "moved",
            Leg::Bumped => "bumped",
            Leg::Loaded => "loaded",
            Leg::Effort => "effort",
            Leg::EffortLoaded => "effort-loaded",
        }
    }

    /// The checkout the leg runs in.
    pub(crate) fn checkout(self) -> Checkout {
        match self {
            Leg::Base | Leg::Repeat | Leg::Serial | Leg::Loaded => Checkout::Original,
            Leg::Moved | Leg::Bumped => Checkout::Moved,
            Leg::Control => Checkout::Control,
            Leg::Effort | Leg::EffortLoaded => Checkout::Effort,
        }
    }

    /// Whether the leg runs under the load generator.
    pub(crate) fn loaded(self) -> bool {
        matches!(self, Leg::Loaded | Leg::EffortLoaded)
    }

    /// Whether the leg is the parallelism axis's serial half.
    pub(crate) fn serial(self) -> bool {
        self == Leg::Serial
    }
}

/// Where a leg runs: the caller's checkout, or one of the verb's copies of
/// its workspace under the scratch directory.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Checkout {
    Original,
    /// At `<scratch>/checkouts/moved/elsewhere/deeper/<root name>`; the
    /// `bumped` leg runs in it after the `moved` leg, with versions bumped.
    Moved,
    /// The root `[trust]` table says `backstop = 1`.
    Control,
    /// The root `[trust]` table says `effort = 1`.
    Effort,
}

/// The legs a run of `axes` needs: the control's and each axis's pair.
pub(crate) fn legs_for(axes: &BTreeSet<Axis>) -> BTreeSet<Leg> {
    let mut legs = BTreeSet::from([Leg::Control]);
    for axis in axes {
        let (left, right) = axis.legs();
        legs.insert(left);
        legs.extend(right);
    }
    legs
}

/// The verb's output format.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Format {
    Terminal,
    Json,
}

/// A parsed `targo trust stability` command line.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct StabilityArgs {
    pub(crate) axes: BTreeSet<Axis>,
    /// Another host's target directory (`--against`).
    pub(crate) against: Option<PathBuf>,
    pub(crate) scratch: Option<PathBuf>,
    pub(crate) keep: bool,
    pub(crate) format: Format,
    /// Everything else, for each leg's `check`, in order.
    pub(crate) check_args: Vec<String>,
}

/// What the command line asked for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Parsed {
    Help,
    Run(StabilityArgs),
}

/// Parse the verb's own options; the rest are the legs' check options, which
/// are then validated by the check's own parser and refused where the verb
/// owns the setting or a leg could not honour it.
pub(crate) fn parse_args(args: &[String]) -> Result<Parsed, String> {
    let mut axes: Option<BTreeSet<Axis>> = None;
    let mut against = None;
    let mut scratch = None;
    let mut keep = false;
    let mut format = Format::Terminal;
    let mut check_args = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let arg = args[index].as_str();
        if arg == "--" {
            check_args.extend(args[index..].iter().cloned());
            break;
        }
        let (flag, inline) = match arg.split_once('=') {
            Some((flag, inline)) if flag.starts_with("--") => (flag, Some(inline.to_string())),
            _ => (arg, None),
        };
        let valued = matches!(flag, "--axes" | "--against" | "--scratch" | "--format");
        let value = if !valued {
            None
        } else if let Some(inline) = inline.clone() {
            Some(inline)
        } else {
            index += 1;
            Some(args.get(index).cloned().ok_or_else(|| format!("{flag} requires a value"))?)
        };
        match (flag, value, inline.is_some()) {
            ("-h" | "--help", None, false) => return Ok(Parsed::Help),
            ("--keep", None, false) => keep = true,
            ("--json", None, false) => format = Format::Json,
            ("--axes", Some(value), _) => axes = Some(parse_axes(&value)?),
            ("--against", Some(value), _) => {
                if against.replace(PathBuf::from(value)).is_some() {
                    return Err("--against is given twice: the host axis compares this host with \
                                one other host's records"
                        .to_string());
                }
            }
            ("--scratch", Some(value), _) => scratch = Some(PathBuf::from(value)),
            ("--format", Some(value), _) => {
                format = match value.as_str() {
                    "terminal" => Format::Terminal,
                    "json" => Format::Json,
                    other => {
                        return Err(format!(
                            "--format `{other}`: stability writes terminal or json"
                        ));
                    }
                }
            }
            _ => check_args.push(args[index].clone()),
        }
        index += 1;
    }
    let axes = match axes {
        Some(axes) => {
            if axes.contains(&Axis::Host) && against.is_none() {
                return Err("the host axis compares this host's run against another host's \
                            records: name them with --against <dir>"
                    .to_string());
            }
            if !axes.contains(&Axis::Host) && against.is_some() {
                return Err("--against is the host axis's input; add `host` to --axes".to_string());
            }
            axes
        }
        None => {
            // §3.8's axes: `effort` is not among them, and fails until
            // KNOWN_HAZARDS BUDGET-1 closes, so it runs only when asked for.
            let mut axes: BTreeSet<Axis> = Axis::ALL
                .into_iter()
                .filter(|axis| !matches!(axis, Axis::Host | Axis::Effort))
                .collect();
            if against.is_some() {
                axes.insert(Axis::Host);
            }
            axes
        }
    };
    validate_check_args(&check_args)?;
    Ok(Parsed::Run(StabilityArgs { axes, against, scratch, keep, format, check_args }))
}

fn parse_axes(list: &str) -> Result<BTreeSet<Axis>, String> {
    let mut axes = BTreeSet::new();
    for name in list.split(',').map(str::trim) {
        let axis = Axis::parse(name).ok_or_else(|| {
            let known: Vec<&str> = Axis::ALL.iter().map(|axis| axis.name()).collect();
            format!("unknown axis `{name}` (axes: {})", known.join(", "))
        })?;
        axes.insert(axis);
    }
    if axes.is_empty() {
        return Err("--axes names no axis".to_string());
    }
    Ok(axes)
}

/// Refuse the check options the verb owns or a leg could not honour, after the
/// check's own parser has accepted them (so a typo is the check's refusal,
/// named as the check names it).
pub(crate) fn validate_check_args(check_args: &[String]) -> Result<(), String> {
    let parsed = crate::cli::parse_subcommand_args(check_args)
        .map_err(|error| format!("check options: {error}"))?;
    let refusal = |what: &str, why: &str| Err(format!("{what} is refused: {why}"));
    if parsed.manifest_path.is_some() {
        return refusal(
            "--manifest-path",
            "run stability from the package's directory; a leg in a copied checkout cannot \
             follow a manifest path back into the original",
        );
    }
    if parsed.is_single_file {
        return refusal(
            "a single-file operand",
            "stability compares the per-package records of a Cargo package",
        );
    }
    if parsed.worker_threads != 0 {
        return refusal(
            "--worker-threads",
            "worker threads are the parallelism axis's, which runs one leg with 1 and one with \
             the default",
        );
    }
    if parsed.report_dir.is_some() {
        return refusal("--report-dir", "every leg would write the same directory");
    }
    if parsed.save_baseline.is_some() || parsed.baseline.is_some() {
        return refusal("--save-baseline/--baseline", "a leg is a check, not a baseline run");
    }
    if parsed.rewrite || parsed.standalone {
        return refusal(
            "--rewrite/--standalone",
            "a leg is one compiler-backed check whose records the verb compares",
        );
    }
    for arg in check_args.iter().take_while(|arg| arg.as_str() != "--") {
        if arg == "--target-dir" || arg.starts_with("--target-dir=") {
            return refusal("--target-dir", "every leg runs in its own target directory");
        }
        if arg == "-j" || arg.starts_with("-j") || arg == "--jobs" || arg.starts_with("--jobs=") {
            return refusal(
                "-j/--jobs",
                "the job count is the parallelism axis's, which runs one leg with 1 and one \
                 with the default",
            );
        }
    }
    let mut args = check_args.iter().take_while(|arg| arg.as_str() != "--");
    while let Some(arg) = args.next() {
        let value = match arg.strip_prefix("--config=") {
            Some(value) => value,
            None if arg == "--config" => match args.next() {
                Some(value) => value.as_str(),
                None => break,
            },
            None => continue,
        };
        for (key, why) in [
            (
                "jobs",
                "the job count is the parallelism axis's, and a --config outranks the serial \
                 leg's CARGO_BUILD_JOBS",
            ),
            ("target-dir", "every leg runs in its own target directory"),
        ] {
            if config_sets_build_key(value, key)? {
                return Err(format!(
                    "a --config that sets build.{key} (`{value}`) is refused: {why}"
                ));
            }
        }
    }
    Ok(())
}

/// Whether a `--config` value sets `build.<key>`. As Cargo reads it: a path
/// to an existing file is a configuration file, anything else a `KEY=VALUE`
/// in TOML's dotted-key form. A file that cannot be read is refused, since
/// what it sets cannot be told; a value that is not TOML is left to the
/// check, which refuses it as Cargo does.
fn config_sets_build_key(value: &str, key: &str) -> Result<bool, String> {
    let path = Path::new(value);
    let text = if !value.is_empty() && path.is_file() {
        std::fs::read_to_string(path).map_err(|error| {
            format!("--config `{value}`: cannot read it to see what it sets: {error}")
        })?
    } else {
        value.to_string()
    };
    let Ok(table) = text.parse::<toml::Table>() else {
        return Ok(false);
    };
    Ok(table
        .get("build")
        .and_then(toml::Value::as_table)
        .is_some_and(|build| build.contains_key(key)))
}

/// `targo trust stability`.
pub(crate) fn run_subcommand(args: &[String]) -> ExitCode {
    let args = match parse_args(args) {
        Ok(Parsed::Help) => {
            print!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        Ok(Parsed::Run(args)) => args,
        Err(error) => {
            eprintln!("targo trust stability: {error}");
            eprintln!("Run `targo trust stability --help` for usage.");
            return ExitCode::from(EXIT_USAGE);
        }
    };
    let exe = match std::env::current_exe() {
        Ok(exe) => exe,
        Err(error) => {
            eprintln!(
                "targo trust stability: cannot name this executable to run the legs: {error}"
            );
            return ExitCode::from(EXIT_USAGE);
        }
    };
    let cwd = match std::env::current_dir() {
        Ok(cwd) => cwd,
        Err(error) => {
            eprintln!("targo trust stability: cannot read the current directory: {error}");
            return ExitCode::from(EXIT_USAGE);
        }
    };
    let mut runner = CheckProcess { exe };
    ExitCode::from(run(&args, &cwd, &mut runner))
}

/// Everything a run of the verb resolved before its first leg.
pub(crate) struct Plan {
    /// What the copies are made of: the workspace and every package directory
    /// it reads by path, below their common root.
    pub(crate) closure: closure::PathClosure,
    /// The caller's directory, relative to the workspace root: each leg runs
    /// at the same place in its checkout.
    pub(crate) relative_cwd: PathBuf,
    /// The private scratch directory.
    pub(crate) scratch: PathBuf,
    pub(crate) legs: BTreeSet<Leg>,
    /// Each leg's check options (`StabilityArgs::check_args`).
    pub(crate) check_args: Vec<String>,
    /// The load generator's busy loops (`legs::load_generator_loops`).
    pub(crate) load_loops: usize,
}

/// Run the verb against the package at `cwd`, every leg through `runner`:
/// the exit status (0, 1, 2 or 3).
pub(crate) fn run(args: &StabilityArgs, cwd: &Path, runner: &mut dyn LegRunner) -> u8 {
    let against = match &args.against {
        Some(dir) => match read_against(dir) {
            Ok(units) => units,
            Err(error) => {
                eprintln!("targo trust stability: --against: {error}");
                return EXIT_USAGE;
            }
        },
        None => BTreeMap::new(),
    };
    let (workspace_root, relative_cwd) = match locate(cwd) {
        Ok(located) => located,
        Err(error) => {
            eprintln!("targo trust stability: {error}");
            return EXIT_USAGE;
        }
    };
    let closure = match closure::path_closure(&workspace_root) {
        Ok(closure) => closure,
        Err(error) => {
            eprintln!("targo trust stability: the workspace cannot be copied: {error}");
            return EXIT_USAGE;
        }
    };
    let scratch_parent = match args.scratch.clone().or_else(default_scratch_parent) {
        Some(parent) => parent,
        None => {
            eprintln!(
                "targo trust stability: neither TMPDIR nor HOME names a directory for the legs; \
                 pass --scratch <dir>"
            );
            return EXIT_USAGE;
        }
    };
    // The scratch directory by the file system's own name, as the workspace
    // root is: a copy leaves it out by comparing paths, and a copy into the
    // tree it copies, or a leg in the caller's checkout that sees the copies,
    // is refused outright. The tree copied is the closure's root: the
    // workspace, and every directory it reads by path, below it.
    let scratch_parent = match scratch_parent.canonicalize() {
        Ok(parent) if parent.starts_with(&closure.root) => {
            let what = if closure.is_self_contained() {
                format!("inside the workspace `{}`", workspace_root.display())
            } else {
                format!(
                    "inside `{}`, the copy's root (the nearest directory that holds the workspace \
                     `{}` and everything it reads by path; it is there because of {})",
                    closure.root.display(),
                    workspace_root.display(),
                    closure.reached_through.join(", ")
                )
            };
            eprintln!(
                "targo trust stability: the scratch directory `{}` is {what}: the copies would be \
                 part of the tree they copy; pass --scratch outside it",
                parent.display()
            );
            return EXIT_USAGE;
        }
        Ok(parent) => parent,
        Err(error) => {
            eprintln!(
                "targo trust stability: cannot resolve the scratch directory `{}`: {error}",
                scratch_parent.display()
            );
            return EXIT_USAGE;
        }
    };
    let scratch =
        match tempfile::Builder::new().prefix("trust-stability.").tempdir_in(&scratch_parent) {
            Ok(scratch) => scratch,
            Err(error) => {
                eprintln!(
                    "targo trust stability: cannot create a scratch directory in `{}`: {error}",
                    scratch_parent.display()
                );
                return EXIT_USAGE;
            }
        };
    let plan = Plan {
        closure,
        relative_cwd,
        scratch: scratch.path().to_path_buf(),
        legs: legs_for(&args.axes),
        check_args: args.check_args.clone(),
        load_loops: legs::load_generator_loops(),
    };
    let report = execute(args, &plan, against, runner);
    match args.format {
        Format::Terminal => print!("{}", report.render_terminal()),
        Format::Json => println!(
            "{}",
            serde_json::to_string_pretty(&report.render_json()).expect("a JSON value serializes")
        ),
    }
    if args.keep {
        let kept = scratch.keep();
        eprintln!("targo trust stability: kept `{}`", kept.display());
    }
    report.exit
}

/// Another host's records (`--against`): the packages its check recorded in
/// the target directory carried here (`legs::read_records`). A directory with
/// no package record names nothing to compare, which is a usage error.
fn read_against(dir: &Path) -> Result<BTreeMap<String, UnitFacts>, String> {
    let units = legs::read_records(dir)?;
    if units.is_empty() {
        return Err(format!(
            "`{}` holds no package record (`{}`): name the directory that holds the `trust` \
             directory `targo trust check` wrote into its target directory",
            dir.display(),
            crate::package_record::package_records_dir(dir).display()
        ));
    }
    Ok(units)
}

/// The default parent of the scratch directory: `$TMPDIR`, else `$HOME`
/// (never a guess at `/tmp`, which is shared and world-writable).
fn default_scratch_parent() -> Option<PathBuf> {
    ["TMPDIR", "HOME"]
        .into_iter()
        .filter_map(std::env::var_os)
        .find(|value| !value.is_empty())
        .map(PathBuf::from)
}

/// The workspace root governing `cwd`, and `cwd` relative to it, both read
/// through the file system's own names (`canonicalize`): each leg runs at that
/// relative place in its checkout, so that Cargo selects there what it selects
/// here.
fn locate(cwd: &Path) -> Result<(PathBuf, PathBuf), String> {
    let canonical = |path: &Path| {
        path.canonicalize().map_err(|error| format!("cannot resolve `{}`: {error}", path.display()))
    };
    let cwd = canonical(cwd)?;
    let root = canonical(&workspace_root(&cwd)?)?;
    let relative = cwd.strip_prefix(&root).map(Path::to_path_buf).map_err(|_| {
        format!(
            "`{}` is not under its workspace root `{}`: run stability from inside the workspace",
            cwd.display(),
            root.display()
        )
    })?;
    Ok((root, relative))
}

/// The workspace root governing `cwd`: the directory of the manifest whose
/// `[trust]` table is its policy (`config::policy_manifest`).
fn workspace_root(cwd: &Path) -> Result<PathBuf, String> {
    crate::config::workspace_root_dir(cwd).map_err(|error| error.to_string())?.ok_or_else(|| {
        format!(
            "no Cargo manifest at or above `{}`: run stability from a package's directory",
            cwd.display()
        )
    })
}

/// What one leg produced.
#[derive(Clone, Debug)]
pub(crate) struct LegRun {
    pub(crate) leg: Leg,
    /// The directory the leg ran in.
    pub(crate) cwd: PathBuf,
    /// The leg's exit status, when it exited.
    pub(crate) exit: Option<i32>,
    /// Its packages, from its records; why it did not run, when it did not.
    pub(crate) side: Side,
    /// For a loaded leg: the busy loops asked for, and how many still ran
    /// when the leg ended.
    pub(crate) load: Option<(usize, usize)>,
    /// The tail of the leg's stderr, when it did not run or wrote no record.
    pub(crate) stderr_tail: Option<String>,
    /// Wall-clock seconds the leg took (stated, compared nowhere).
    pub(crate) seconds: f64,
}

/// The verb's findings.
pub(crate) struct Report {
    /// The scratch directory, when it is kept (`--keep`).
    pub(crate) scratch: Option<PathBuf>,
    /// What every copy carried.
    pub(crate) copy: closure::PathClosure,
    pub(crate) legs: Vec<LegRun>,
    pub(crate) control: ControlResult,
    pub(crate) axes: Vec<AxisResult>,
    pub(crate) exit: u8,
}

/// Run every leg of `plan` in order, then judge the control and each axis.
pub(crate) fn execute(
    args: &StabilityArgs,
    plan: &Plan,
    against: BTreeMap<String, UnitFacts>,
    runner: &mut dyn LegRunner,
) -> Report {
    let mut checkouts: BTreeMap<Checkout, Result<PathBuf, String>> = BTreeMap::new();
    let mut runs: BTreeMap<Leg, LegRun> = BTreeMap::new();
    let count = plan.legs.len();
    for (index, leg) in plan.legs.iter().copied().enumerate() {
        eprintln!("targo trust stability: leg {}/{count} `{}`: running", index + 1, leg.label());
        let recorded: BTreeSet<String> = match leg {
            Leg::Bumped => runs
                .get(&Leg::Moved)
                .map(|moved| moved.side.units.keys().cloned().collect())
                .unwrap_or_default(),
            _ => BTreeSet::new(),
        };
        let run = legs::run_leg(leg, plan, args.keep, &mut checkouts, runner, &recorded);
        eprintln!(
            "targo trust stability: leg `{}`: {} in {:.1}s",
            leg.label(),
            match (&run.side.failure, run.exit) {
                (Some(failure), _) => format!("could not run: {failure}"),
                (None, Some(code)) =>
                    format!("exit {code}, {} package record(s)", run.side.units.len()),
                (None, None) => "ended without an exit status".to_string(),
            },
            run.seconds
        );
        runs.insert(leg, run);
    }
    let control = judge::judge_control(&runs[&Leg::Control].side);
    let other_host = Side {
        label: "another host".to_string(),
        failure: None,
        units: against,
        cargo_configs: None,
    };
    let axes: Vec<AxisResult> = args
        .axes
        .iter()
        .map(|axis| {
            let (left, right) = axis.legs();
            let right = match right {
                Some(right) => &runs[&right].side,
                None => &other_host,
            };
            let load = match axis {
                Axis::Load => runs.get(&Leg::Loaded).and_then(|run| run.load),
                Axis::Effort => runs.get(&Leg::EffortLoaded).and_then(|run| run.load),
                _ => None,
            };
            judge::judge_axis(*axis, &runs[&left].side, right, load)
        })
        .collect();
    let exit = judge::exit_status(&control, &axes);
    Report {
        scratch: args.keep.then(|| plan.scratch.clone()),
        copy: plan.closure.clone(),
        legs: runs.into_values().collect(),
        control,
        axes,
        exit,
    }
}

#[cfg(test)]
mod tests;
