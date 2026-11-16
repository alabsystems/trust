//! Controls for `targo trust gate corpus-delta`, through the command's own
//! path over a checkout on disk. The compilers are stand-ins: a [`FakeRunner`]
//! writes the log a compiler would and says how it exited, by the name of the
//! compiler it was handed. The real process runner, against fake compilers on
//! disk, is `targo-trust/tests/corpus_delta_cli.rs`.
//!
//! The bracketed numbers are the checks of the shell test this replaces
//! (`scripts/tests/seal_corpus_delta_test.sh`, deleted with the script).

use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use super::cli::{Host, run_with};
use super::identity::{CompilerProbe, VersionProbe};
use super::run::{CaseExit, CaseRunner, CaseSpec};
use super::{CaseRecord, FlipKind, Pin, RankFn, Verdict, compare_with, gate_args, rank, table};
use crate::durable_io;

/// What a row asks beyond an exit status (a text in the output, a `conditional`
/// pin, a dependency), the three corpora that ask it, and their scripts.
mod cases;

/// The fixture checkout's HEAD, as the probe reports it.
const HEAD: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
/// The sweep file the `*-one` compilers single out.
const VICTIM: &str = "a.rs";
const SWEEP: [&str; 3] = ["a", "b", "c"];
/// The fixture battery: every case pinned `refuses` but p07.
const BATTERY: [&str; 4] = ["p01", "p02", "p03", "p07"];

const TABLE_TEXT: &str = r#"schema = "trust.corpora.v1"

[[corpus]]
id = "sweep"
glob = "corpora/sweep/*.rs"
args = ["--crate-type=lib", "--edition", "2021"]

[[corpus]]
id = "battery"
glob = "corpora/battery/*.rs"
args = ["--crate-type=lib", "--edition", "2021"]
pin = "refuses"
pins = { p07 = "verifies" }

[[corpus]]
id = "lean"
args = ["--crate-type=lib", "--edition", "2021"]

[[corpus.case]]
id = "island"
file = "corpora/lean/island.rs"
args = ["-Z", "trust-verify=off", "--crate-type=lib", "--edition", "2024"]
pin = "verifies"

[[not_on_yet]]
id = "bench"
script = "scripts/daily_driver_bench.sh"
why = "its sources are written inline in the script"
"#;

/// Every fake compiler's name: how it treats a case ([`FakeRunner`]) and what
/// it answers `-vV` with ([`FakeProbe`]).
const COMPILERS: [&str; 16] = [
    "accept",
    "refuse-one",
    "crash-one",
    "segv-one",
    "refuse-all",
    "hang-one",
    "hang-all",
    "refuse-a-hang-b",
    "unstartable",
    "drop-b",
    "silent",
    "long-cause",
    "broken",
    "anonymous",
    "at-head",
    "squatter",
];

/// A compiler's `commit-hash`: one digit, forty times.
fn commit(compiler: &str) -> String {
    let digit = match compiler {
        "accept" => "1",
        "refuse-one" => "2",
        "crash-one" => "3",
        "refuse-all" => "4",
        "at-head" => return HEAD.to_owned(),
        _ => "9",
    };
    digit.repeat(40)
}

fn name(path: &Path) -> &str {
    path.file_name().and_then(|name| name.to_str()).expect("a fixture path has a UTF-8 name")
}

/// Stands in for the compiler process: writes the case's log and says how the
/// compile ended.
#[derive(Default)]
struct FakeRunner {
    specs: Vec<CaseSpec>,
}

impl CaseRunner for FakeRunner {
    fn run(&mut self, spec: &CaseSpec) -> Option<CaseExit> {
        self.specs.push(spec.clone());
        let compiler = name(&spec.compiler);
        let file = name(&spec.source);
        if compiler == "silent" || (compiler == "drop-b" && file == "b.rs") {
            return None;
        }
        let victim = file == VICTIM;
        let (exit, log) = match compiler {
            "refuse-all" => (CaseExit::Exited(1), "error: fake refusal\n".to_owned()),
            "refuse-one" | "refuse-a-hang-b" if victim => (
                CaseExit::Exited(1),
                format!(
                    "warning: unused\n  error: indented, so not the cause\nerror: fake \
                     refuse-one of {file}\nerror: a second error\n"
                ),
            ),
            "refuse-a-hang-b" if file == "b.rs" => (CaseExit::PastBound, String::new()),
            "crash-one" if victim => {
                (CaseExit::Exited(101), format!("error: fake crash-one of {file}\n"))
            }
            "segv-one" if victim => (CaseExit::Signalled(11), String::new()),
            "long-cause" if victim => {
                (CaseExit::Exited(1), format!("error:\t{}\n", "x".repeat(400)))
            }
            "hang-one" if victim => (CaseExit::PastBound, String::new()),
            "hang-all" => (CaseExit::PastBound, String::new()),
            "unstartable" if victim => {
                (CaseExit::Failed("cannot start the compiler: it is gone".into()), String::new())
            }
            _ => (CaseExit::Exited(0), String::new()),
        };
        fs::write(&spec.log, log).expect("the verb creates the log's directory");
        Some(exit)
    }
}

/// Stands in for `-vV` and for the checkout's HEAD.
struct FakeProbe;

impl CompilerProbe for FakeProbe {
    fn verbose_version(&mut self, compiler: &Path, log: &Path) -> VersionProbe {
        let compiler = name(compiler);
        if compiler == "squatter" {
            // Leaves a directory where its side's record goes.
            fs::create_dir_all(log.with_file_name("record.ndjson")).unwrap();
        }
        let (exit, output) = match compiler {
            "broken" => (CaseExit::Exited(1), "dyld: Library not loaded\n".to_owned()),
            "anonymous" => (
                CaseExit::Exited(0),
                "rustc 0.0.0-fake\nbinary: trustc\ncommit-hash: unknown\n".to_owned(),
            ),
            _ => (
                CaseExit::Exited(0),
                format!(
                    "rustc 0.0.0-fake\nbinary: trustc\ncommit-hash: {}\ncommit-date: 2026-01-01\n",
                    commit(compiler)
                ),
            ),
        };
        VersionProbe { exit, output }
    }

    fn checkout_head(&mut self, _root: &Path) -> Option<String> {
        Some(HEAD.to_owned())
    }
}

/// What one run of the verb did.
struct Run {
    code: u8,
    text: String,
    /// Every case the verb handed its runner, in order.
    specs: Vec<CaseSpec>,
    progress: Vec<String>,
}

impl Run {
    fn has_line(&self, line: &str) -> bool {
        self.text.lines().any(|candidate| candidate == line)
    }

    /// The flip lines, as the shell test counted them.
    fn flips(&self) -> Vec<&str> {
        self.text
            .lines()
            .filter(|line| {
                ["LOSS ", "GAIN ", "GONE ", "NEW "].iter().any(|kind| line.starts_with(kind))
            })
            .collect()
    }
}

/// A checkout with a table, three corpora and one file per fake compiler.
struct World {
    root: tempfile::TempDir,
}

impl World {
    fn new() -> Self {
        Self::with_table(TABLE_TEXT)
    }

    fn with_table(table: &str) -> Self {
        let world = Self { root: tempfile::tempdir().unwrap() };
        world.write("tests/corpora.toml", table);
        for case in SWEEP {
            world.write(&format!("corpora/sweep/{case}.rs"), "pub fn f() {}\n");
        }
        for case in BATTERY {
            world.write(&format!("corpora/battery/{case}.rs"), "pub fn f() { panic!() }\n");
        }
        // R2: one Rust file with a Lean island, compiled with its own arguments.
        world.write(
            "corpora/lean/island.rs",
            "clean {\n  theorem t : True := trivial\n}\n\npub fn f() {}\n",
        );
        world.write("scripts/daily_driver_bench.sh", "#!/bin/sh\n");
        for compiler in COMPILERS {
            world.write(&format!("bin/{compiler}"), "");
            executable(&world.path(&format!("bin/{compiler}")));
        }
        world
    }

    fn path(&self, relative: &str) -> PathBuf {
        self.root.path().join(relative)
    }

    fn write(&self, relative: &str, text: &str) {
        let path = self.path(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    /// Run the verb with exactly `args`, from the checkout's root.
    fn run_ranked(&self, args: &[String], rank: RankFn) -> Run {
        let mut runner = FakeRunner::default();
        let mut lines = Vec::new();
        let mut progress = |line: &str| lines.push(line.to_owned());
        let (code, text) = run_with(
            args,
            &mut Host {
                cwd: self.root.path().to_path_buf(),
                runner: &mut runner,
                probe: &mut FakeProbe,
                progress: &mut progress,
                rank,
            },
        );
        Run { code, text, specs: runner.specs, progress: lines }
    }

    fn args(&self, old: &str, new: &str, rest: &[&str]) -> Vec<String> {
        let mut args = vec![
            "--old".to_owned(),
            self.path(&format!("bin/{old}")).display().to_string(),
            "--new".to_owned(),
            self.path(&format!("bin/{new}")).display().to_string(),
        ];
        args.extend(rest.iter().map(|arg| (*arg).to_owned()));
        args
    }

    /// The delta from compiler `old` to compiler `new`.
    fn delta(&self, old: &str, new: &str, rest: &[&str]) -> Run {
        self.run_ranked(&self.args(old, new, rest), rank)
    }

    /// One side's kept record.
    fn kept(&self, keep: &str, side: &str) -> Vec<CaseRecord> {
        fs::read_to_string(self.path(keep).join(side).join("record.ndjson"))
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect()
    }
}

/// One corpus's line of the counts: as pinned / recorded, old then new.
fn row(corpus: &str, old: (usize, usize), new: (usize, usize)) -> String {
    format!("{corpus:<10} {:>8} / {:<4} {:>8} / {}", old.0, old.1, new.0, new.1)
}

fn executable(path: &Path) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
    }
    #[cfg(not(unix))]
    let _ = path;
}

// --- an unpinned corpus: verifies is best ------------------------------------

/// [1-5]
#[test]
fn a_case_that_stops_verifying_is_one_loss_naming_its_error() {
    let world = World::new();
    let run = world.delta("accept", "refuse-one", &["--corpora", "sweep,battery"]);
    assert_eq!(run.code, 0, "a loss without --fail-on-loss exits 0:\n{}", run.text);
    assert_eq!(run.flips().len(), 1, "{}", run.text);
    assert!(
        run.has_line("LOSS  sweep/a: verifies -> refuses: error: fake refuse-one of a.rs"),
        "{}",
        run.text
    );
    assert!(run.text.contains(&commit("accept")) && run.text.contains(&commit("refuse-one")));
    assert!(run.has_line("seal corpus delta: 1 lost, 0 gained"), "{}", run.text);
    assert!(run.has_line(&row("sweep", (3, 3), (2, 3))), "{}", run.text);
    assert!(run.has_line(&row("battery", (1, 4), (1, 4))), "{}", run.text);
    assert!(run.has_line("corpus      old as pinned  new as pinned"), "{}", run.text);
}

/// [6-8]
#[test]
fn fail_on_loss_exits_1_for_a_loss_and_0_for_a_gain() {
    let world = World::new();
    let lost = world.delta("accept", "refuse-one", &["--fail-on-loss", "--corpora", "sweep"]);
    assert_eq!(lost.code, 1, "{}", lost.text);
    let gained = world.delta("refuse-one", "accept", &["--fail-on-loss", "--corpora", "sweep"]);
    assert_eq!(gained.code, 0, "{}", gained.text);
    assert_eq!(
        gained.flips(),
        ["GAIN  sweep/a: refuses -> verifies (was: error: fake refuse-one of a.rs)"]
    );
    assert!(gained.has_line("seal corpus delta: 0 lost, 1 gained"), "{}", gained.text);
}

/// [9]
#[test]
fn identical_compilers_print_no_flip() {
    let world = World::new();
    let run = world.delta("accept", "accept", &["--fail-on-loss"]);
    assert_eq!(run.code, 0, "{}", run.text);
    assert!(run.flips().is_empty(), "{}", run.text);
    assert!(run.has_line("seal corpus delta: 0 lost, 0 gained"), "{}", run.text);
}

// --- crashes -------------------------------------------------------------------

/// [10-11]
#[test]
fn a_clean_refusal_that_becomes_a_crash_is_a_loss() {
    let world = World::new();
    let run = world.delta("refuse-one", "crash-one", &["--fail-on-loss", "--corpora", "sweep"]);
    assert_eq!(run.code, 1, "{}", run.text);
    assert_eq!(
        run.flips(),
        ["LOSS  sweep/a: refuses -> crash:101: error: fake crash-one of a.rs"],
        "{}",
        run.text
    );
    assert!(run.has_line("the new compiler crashed on 1 case(s)"), "{}", run.text);
}

#[test]
fn a_compiler_ended_by_a_signal_is_a_crash_of_128_plus_the_signal() {
    let world = World::new();
    let run = world.delta("accept", "segv-one", &["--corpora", "sweep"]);
    assert_eq!(
        run.flips(),
        ["LOSS  sweep/a: verifies -> crash:139: no `error` line in its output"],
        "{}",
        run.text
    );
}

/// A crash that changes its status has not changed its rank.
#[test]
fn two_crashes_of_one_rank_print_nothing() {
    let world = World::new();
    let run = world.delta("crash-one", "segv-one", &["--fail-on-loss", "--corpora", "sweep"]);
    assert_eq!(run.code, 0, "{}", run.text);
    assert!(run.flips().is_empty(), "{}", run.text);
    assert!(run.has_line("the new compiler crashed on 1 case(s)"), "{}", run.text);
}

// --- pins: the battery pins every case but p07 `refuses` ----------------------

/// One of checks [12-14]: a run over the battery and what must hold of it.
struct PinCheck {
    what: &'static str,
    old: &'static str,
    new: &'static str,
    holds: fn(&Run) -> bool,
}

fn must_refuse_case_that_verifies_is_a_loss(run: &Run) -> bool {
    run.code == 1
        && run.has_line(
            "LOSS  battery/p01: refuses -> verifies (pinned refuses): a case pinned refuses now \
             verifies",
        )
}

fn every_case_but_p07_is_lost_and_p07_is_the_gain(run: &Run) -> bool {
    run.has_line(&format!("seal corpus delta: {} lost, 1 gained", BATTERY.len() - 1))
        && run.has_line(
            "GAIN  battery/p07: refuses -> verifies (pinned verifies) (was: error: fake refusal)",
        )
}

fn the_direction_back_is_gains_and_one_loss(run: &Run) -> bool {
    run.code == 1
        && run.has_line(&format!("seal corpus delta: 1 lost, {} gained", BATTERY.len() - 1))
        && run.has_line(
            "LOSS  battery/p07: verifies -> refuses (pinned verifies): error: fake refusal",
        )
}

const PIN_CHECKS: [PinCheck; 3] = [
    PinCheck {
        what: "[12] a must-refuse case that starts verifying is a LOSS, not a GAIN",
        old: "refuse-all",
        new: "accept",
        holds: must_refuse_case_that_verifies_is_a_loss,
    },
    PinCheck {
        what: "[13] every battery case but p07 is lost, and p07 is the one gain",
        old: "refuse-all",
        new: "accept",
        holds: every_case_but_p07_is_lost_and_p07_is_the_gain,
    },
    PinCheck {
        what: "[14] the pinned direction back is a GAIN for each must-refuse case and one LOSS",
        old: "accept",
        new: "refuse-all",
        holds: the_direction_back_is_gains_and_one_loss,
    },
];

fn pin_check_run(world: &World, check: &PinCheck, rank: RankFn) -> Run {
    world.run_ranked(
        &world.args(check.old, check.new, &["--fail-on-loss", "--corpora", "battery"]),
        rank,
    )
}

/// [12-14]
#[test]
fn a_verdict_is_ranked_against_its_pin() {
    let world = World::new();
    for check in &PIN_CHECKS {
        let run = pin_check_run(&world, check, rank);
        assert!((check.holds)(&run), "{}:\n{}", check.what, run.text);
    }
}

/// A rank that ignores the pin: `verifies` is always best.
fn pin_blind_rank(verdict: Verdict, _pin: Option<Pin>) -> Option<i8> {
    rank(verdict, None)
}

/// The mutant control for [12-14]: under a rank that cannot see a pin, each of
/// the three checks must fail to match. A check that still held would not be
/// about pins.
#[test]
fn pin_blind_rank_is_caught() {
    let world = World::new();
    for check in &PIN_CHECKS {
        let run = pin_check_run(&world, check, pin_blind_rank);
        assert!(!(check.holds)(&run), "a pin-blind rank passes {}:\n{}", check.what, run.text);
    }
}

#[test]
fn rank_puts_a_false_proof_below_a_crash_below_a_miss_below_the_pin() {
    use Verdict::{Crash, NotJudged, Refuses, Verifies};
    let (verifies, refuses) = (Some(Pin::Verifies), Some(Pin::Refuses));
    assert_eq!(rank(Verifies, None), Some(2));
    assert_eq!(rank(Refuses, None), Some(1));
    assert_eq!(rank(Crash(101), None), Some(0));
    assert_eq!(rank(Verifies, verifies), Some(2));
    assert_eq!(rank(Refuses, verifies), Some(1));
    assert_eq!(rank(Crash(139), verifies), Some(0));
    assert_eq!(rank(Refuses, refuses), Some(2));
    assert_eq!(rank(Crash(101), refuses), Some(0));
    assert_eq!(rank(Verifies, refuses), Some(-1));
    for pin in [None, verifies, refuses] {
        assert_eq!(rank(NotJudged, pin), None, "a case that was not judged has no rank");
    }
}

// --- compilers that cannot run, and arguments ----------------------------------

/// [15] [16]
#[test]
fn a_path_that_is_no_executable_file_is_a_usage_error() {
    let world = World::new();
    world.write("bin/data", "not a program\n");
    fs::create_dir_all(world.path("bin/a-directory")).unwrap();
    for absent in ["absent", "a-directory", "data"] {
        let run = world.delta("accept", absent, &["--corpora", "sweep"]);
        assert_eq!(run.code, 2, "{absent}:\n{}", run.text);
        assert!(run.text.contains("no executable compiler at"), "{}", run.text);
        assert!(run.specs.is_empty(), "{absent}: no case may run");
    }
}

/// [17]
#[test]
fn a_compiler_that_does_not_answer_its_version_could_not_run() {
    let world = World::new();
    let run = world.delta("accept", "broken", &["--corpora", "sweep"]);
    assert_eq!(run.code, 3, "{}", run.text);
    assert!(run.text.contains("COULD NOT RUN"), "{}", run.text);
    assert!(run.text.contains("does not run: `-vV` exited 1"), "{}", run.text);
    assert!(run.text.contains("dyld: Library not loaded"), "{}", run.text);
    assert!(run.flips().is_empty(), "{}", run.text);
    assert!(run.specs.is_empty(), "no case may run before both compilers answer");
    // Critique 6: the refusal still says what the run was not going to compare.
    assert!(run.has_line("not compared: battery, lean (not named by --corpora)"), "{}", run.text);
    assert!(
        run.has_line(
            "not compared: bench (not in tests/corpora.toml yet: scripts/daily_driver_bench.sh)"
        ),
        "{}",
        run.text
    );
    assert!(
        run.text.ends_with("  dyld: Library not loaded\n"),
        "the refusal is last:\n{}",
        run.text
    );
}

/// [18]
#[test]
fn an_unknown_corpus_is_a_usage_error() {
    let world = World::new();
    for (list, why) in [
        ("nonsense", "unknown corpus: \"nonsense\" (the table has: sweep, battery, lean)"),
        ("sweep,", "unknown corpus: \"\""),
        ("sweep,sweep", "--corpora names sweep twice"),
        ("bench", "corpus bench is not in tests/corpora.toml yet (scripts/daily_driver_bench.sh"),
    ] {
        let run = world.delta("accept", "accept", &["--corpora", list]);
        assert_eq!(run.code, 2, "{list}:\n{}", run.text);
        assert!(run.text.contains(why), "{list}:\n{}", run.text);
        assert!(run.specs.is_empty());
    }
}

#[test]
fn arguments_are_named_and_each_is_given_once() {
    let world = World::new();
    let accept = world.path("bin/accept").display().to_string();
    let old: &str = &accept;
    for (args, why) in [
        (vec!["--old", old], "--new is required"),
        (vec!["--new", old], "--old is required"),
        (vec![old, old], "unknown argument"),
        (vec!["--old", old, "--new", old, "--old", old], "--old is given twice"),
        (vec!["--old", old, "--new", old, "--case-seconds", "0"], "--case-seconds"),
        (vec!["--old", old, "--new", old, "--case-seconds", "soon"], "--case-seconds"),
        (vec!["--old", old, "--new", old, "--fail-on-loss=yes"], "takes no value"),
        (vec!["--old", old, "--new"], "--new requires a value"),
        (vec!["--old", old, "--new", old, "--frobnicate"], "unknown argument"),
    ] {
        let args: Vec<String> = args.into_iter().map(str::to_owned).collect();
        let run = world.run_ranked(&args, rank);
        assert_eq!(run.code, 2, "{args:?}:\n{}", run.text);
        assert!(run.text.contains(why), "{args:?}:\n{}", run.text);
        assert!(run.text.contains("Usage: targo trust gate corpus-delta"), "{}", run.text);
    }
    let help = world.run_ranked(&["--help".to_owned()], rank);
    assert_eq!(help.code, 0);
    assert!(help.text.starts_with("Usage: targo trust gate corpus-delta"), "{}", help.text);
}

#[test]
fn gate_arguments_take_either_spelling_of_a_value() {
    let parse = |args: &[&str]| {
        let args: Vec<String> = args.iter().map(|arg| (*arg).to_owned()).collect();
        gate_args::parse(&args, &["--state", "--keep"], &["--strict"])
    };
    let spaced = parse(&["--state", "dir", "--strict"]).unwrap().unwrap();
    assert_eq!(spaced.value("--state"), Some("dir"));
    assert!(spaced.flag("--strict"));
    assert_eq!(spaced.value("--keep"), None);
    let inline = parse(&["--state=a=b"]).unwrap().unwrap();
    assert_eq!(inline.value("--state"), Some("a=b"));
    assert!(!inline.flag("--strict"));
    assert!(parse(&["-h"]).unwrap().is_none());
    assert!(parse(&["--state", "dir", "--help"]).unwrap().is_none());
    let refused: [&[&str]; 8] = [
        &["--state"],
        &["--state="],
        &["--state", "--strict"],
        &["--state", "a", "--state", "b"],
        &["--strict", "--strict"],
        &["--strict=1"],
        &["--help=1"],
        &["operand"],
    ];
    for args in refused {
        assert!(parse(args).is_err(), "{args:?} must be refused");
    }
}

/// [19], for the paths the verb resolves itself. The process side of it is
/// `corpus_delta_cli.rs`.
#[test]
fn relative_paths_resolve_against_the_callers_directory() {
    let world = World::new();
    let args: Vec<String> = [
        "--old",
        "bin/accept",
        "--new",
        "bin/refuse-one",
        "--corpora=sweep",
        "--keep",
        "kept",
        "--repo-root",
        ".",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    let run = world.run_ranked(&args, rank);
    assert_eq!(run.code, 0, "{}", run.text);
    assert_eq!(run.flips().len(), 1, "{}", run.text);
    assert!(run.specs.iter().all(|spec| spec.compiler.is_absolute() && spec.log.is_absolute()));
    assert!(world.path("kept/new/record.ndjson").is_file());
}

// --- the report ----------------------------------------------------------------

#[test]
fn the_report_names_both_compilers_and_whether_they_are_this_checkout() {
    let world = World::new();
    let run = world.delta("accept", "at-head", &["--corpora", "sweep"]);
    let old = world.path("bin/accept").display().to_string();
    let expected = format!(
        "old: rustc 0.0.0-fake | {} 2026-01-01\n     {old}\n     NOTE: the old compiler was \
         built from 1111111111, not this checkout's HEAD aaaaaaaaaa\nnew: rustc 0.0.0-fake | \
         {HEAD} 2026-01-01\n     {}\ncorpora: sweep (this checkout, aaaaaaaaaa)\n",
        commit("accept"),
        world.path("bin/at-head").display()
    );
    assert!(run.text.starts_with(&expected), "{}", run.text);
    let anonymous = world.delta("anonymous", "accept", &["--corpora", "sweep"]);
    assert!(
        anonymous.has_line("old: rustc 0.0.0-fake | unknown")
            && anonymous.has_line(
                "     NOTE: the old compiler names no commit, so its counts cannot be tied to a \
                 tree"
            ),
        "{}",
        anonymous.text
    );
}

/// Critique 6: a run says which daily-driver corpora it did not compare.
#[test]
fn every_run_names_the_corpora_it_did_not_compare() {
    let world = World::new();
    let all = world.delta("accept", "accept", &[]);
    assert!(all.has_line("corpora: sweep, battery, lean (this checkout, aaaaaaaaaa)"));
    assert!(
        all.has_line(
            "not compared: bench (not in tests/corpora.toml yet: scripts/daily_driver_bench.sh)"
        ),
        "{}",
        all.text
    );
    assert!(!all.text.contains("not named by --corpora"), "{}", all.text);
    let one = world.delta("accept", "accept", &["--corpora", "battery"]);
    assert!(one.has_line("not compared: sweep, lean (not named by --corpora)"), "{}", one.text);
    assert!(one.text.contains("not compared: bench (not in"), "{}", one.text);
    // Refusals after the header carry it too.
    let stopped = world.delta("accept", "unstartable", &["--corpora", "sweep"]);
    assert!(stopped.text.contains("not compared: bench (not in"), "{}", stopped.text);

    // So does every run that stops before its header, once the table and
    // `--corpora` are read: each line once, whatever the exit.
    world.write("kept/earlier.txt", "");
    let keep = world.path("kept").display().to_string();
    let before_the_header: [(&str, &str, &[&str], u8); 3] = [
        ("accept", "broken", &["--corpora", "sweep"], 3),
        ("accept", "absent", &["--corpora", "sweep"], 2),
        ("accept", "accept", &["--corpora", "sweep", "--keep", &keep], 2),
    ];
    for (old, new, rest, code) in before_the_header {
        let run = world.delta(old, new, rest);
        assert_eq!(run.code, code, "{new} {rest:?}:\n{}", run.text);
        assert!(run.specs.is_empty(), "{new} {rest:?}: no case may run");
        assert!(!run.text.contains("corpora: "), "{new} {rest:?} has no header:\n{}", run.text);
        for line in [
            "not compared: battery, lean (not named by --corpora)",
            "not compared: bench (not in tests/corpora.toml yet: scripts/daily_driver_bench.sh)",
        ] {
            let times = run.text.lines().filter(|candidate| *candidate == line).count();
            assert_eq!(times, 1, "{new} {rest:?}: `{line}`:\n{}", run.text);
        }
    }
    // The boundary USAGE states: a run refused before its `--corpora` is
    // accepted has chosen nothing, and names none.
    let unchosen = world.delta("accept", "accept", &["--corpora", "nonsense"]);
    assert_eq!(unchosen.code, 2, "{}", unchosen.text);
    assert!(!unchosen.text.contains("not compared:"), "{}", unchosen.text);
}

#[test]
fn the_old_compiler_runs_every_corpus_before_the_new_one_starts() {
    let world = World::new();
    let run = world.delta("accept", "refuse-all", &[]);
    let order: Vec<(&str, &str, &str)> = run
        .specs
        .iter()
        .map(|spec| (name(&spec.compiler), spec.corpus.as_str(), spec.case.as_str()))
        .collect();
    let side = |compiler: &'static str| {
        let mut cases: Vec<(&str, &str, &str)> = Vec::new();
        cases.extend(SWEEP.iter().map(|case| (compiler, "sweep", *case)));
        cases.extend(BATTERY.iter().map(|case| (compiler, "battery", *case)));
        cases.push((compiler, "lean", "island"));
        cases
    };
    assert_eq!(order, [side("accept"), side("refuse-all")].concat());
    assert_eq!(
        run.progress,
        [
            "corpus-delta: old: sweep (3 case(s))",
            "corpus-delta: old: battery (4 case(s))",
            "corpus-delta: old: lean (1 case(s))",
            "corpus-delta: new: sweep (3 case(s))",
            "corpus-delta: new: battery (4 case(s))",
            "corpus-delta: new: lean (1 case(s))",
        ]
    );
    // A compiler writes into scratch, never the checkout, and the scratch is
    // gone when the run is.
    for spec in &run.specs {
        assert!(!spec.work.starts_with(world.root.path()), "{}", spec.work.display());
        assert!(!spec.work.exists(), "{} outlived the run", spec.work.display());
        assert_eq!(spec.bound, Duration::from_secs(1800));
    }
}

/// R2: a Rust file with a `clean { }` island is a case like any other, compiled
/// with its own arguments in place of its corpus's.
#[test]
fn a_case_with_a_lean_island_is_compiled_with_its_own_arguments() {
    let world = World::new();
    let run = world.delta("accept", "refuse-all", &["--corpora", "lean", "--fail-on-loss"]);
    assert_eq!(run.code, 1, "{}", run.text);
    assert_eq!(
        run.flips(),
        ["LOSS  lean/island: verifies -> refuses (pinned verifies): error: fake refusal"]
    );
    for spec in &run.specs {
        assert_eq!(spec.args, ["-Z", "trust-verify=off", "--crate-type=lib", "--edition", "2024"]);
        assert_eq!(spec.source, world.path("corpora/lean/island.rs"));
        assert!(fs::read_to_string(&spec.source).unwrap().contains("clean {"));
    }
    let sweep = world.delta("accept", "accept", &["--corpora", "sweep"]);
    assert_eq!(sweep.specs[0].args, ["--crate-type=lib", "--edition", "2021"]);
}

// --- --keep --------------------------------------------------------------------

/// [20-22]
#[test]
fn keep_leaves_both_records_and_refuses_a_directory_in_use() {
    let world = World::new();
    let keep = world.path("kept").display().to_string();
    let run = world.delta("accept", "refuse-one", &["--keep", &keep, "--corpora", "sweep,battery"]);
    assert_eq!(run.code, 0, "{}", run.text);
    for side in ["old", "new"] {
        let text = fs::read_to_string(world.path("kept").join(side).join("record.ndjson")).unwrap();
        assert_eq!(text.lines().count(), SWEEP.len() + BATTERY.len());
        for line in text.lines() {
            let value: serde_json::Value = serde_json::from_str(line).unwrap();
            let mut fields: Vec<&str> =
                value.as_object().unwrap().keys().map(String::as_str).collect();
            fields.sort_unstable();
            assert_eq!(fields, ["case", "cause", "corpus", "pin", "verdict"], "{line}");
            serde_json::from_str::<CaseRecord>(line).unwrap();
            // The control: a sixth field is refused, so the five are the schema.
            let widened = line.replacen('{', "{\"extra\":1,", 1);
            assert!(serde_json::from_str::<CaseRecord>(&widened).is_err(), "{widened}");
        }
    }
    let new = world.kept("kept", "new");
    assert_eq!(
        new[0],
        CaseRecord {
            corpus: "sweep".into(),
            case: "a".into(),
            verdict: Verdict::Refuses,
            cause: "error: fake refuse-one of a.rs".into(),
            pin: None,
        }
    );
    assert_eq!(new.last().unwrap().pin, Some(Pin::Verifies), "p07");
    assert_eq!(
        fs::read_to_string(world.path("kept/flips.txt")).unwrap(),
        "LOSS  sweep/a: verifies -> refuses: error: fake refuse-one of a.rs\n"
    );
    assert!(
        fs::read_to_string(world.path("kept/summary.txt"))
            .unwrap()
            .ends_with("\nseal corpus delta: 1 lost, 0 gained\n")
    );
    assert!(world.path("kept/new/sweep/a.log").is_file());

    let again = world.delta("accept", "accept", &["--keep", &keep, "--corpora", "sweep"]);
    assert_eq!(again.code, 2, "{}", again.text);
    assert!(again.text.contains("is not empty"), "{}", again.text);
    assert!(again.specs.is_empty(), "a refused --keep runs nothing");
}

/// The shell delta took `--keep` through `cd "$keep" && pwd`. The records are
/// written through `durable_io`, which refuses a `..` component and a symlink
/// its caller could retarget, so the verb resolves the directory first: these
/// two spellings must run, not be refused once the old side has compiled.
#[test]
fn keep_is_resolved_before_anything_is_written() {
    let world = World::new();
    // The controls: unresolved, each spelling is one `durable_io` refuses.
    fs::create_dir_all(world.path("real")).unwrap();
    #[cfg(unix)]
    std::os::unix::fs::symlink(world.path("real"), world.path("link")).unwrap();
    let mut spellings = vec![("sub/../kept", "kept")];
    if cfg!(unix) {
        spellings.push(("link/kept", "real/kept"));
    }
    for (spelling, _) in &spellings {
        let unresolved = world.path(spelling).join("probe");
        assert!(
            durable_io::atomic_write_private(&unresolved, b"").is_err(),
            "{spelling}: the control must be a path durable_io refuses"
        );
    }
    for (spelling, lands_in) in spellings {
        // Relative to the caller's directory, as typed.
        let run = world.delta("accept", "refuse-one", &["--corpora", "sweep", "--keep", spelling]);
        assert_eq!(run.code, 0, "--keep {spelling}:\n{}", run.text);
        assert_eq!(run.flips().len(), 1, "--keep {spelling}:\n{}", run.text);
        assert_eq!(world.kept(lands_in, "old").len(), SWEEP.len(), "--keep {spelling}");
        assert_eq!(world.kept(lands_in, "new")[0].verdict, Verdict::Refuses, "--keep {spelling}");
        assert!(world.path(lands_in).join("summary.txt").is_file(), "--keep {spelling}");
        let resolved = fs::canonicalize(world.path(lands_in)).unwrap();
        for spec in &run.specs {
            assert!(
                spec.log.starts_with(&resolved),
                "{} for --keep {spelling}",
                spec.log.display()
            );
        }
    }
}

/// A place the records cannot be written to is refused before a case is
/// compiled, as the shell delta created each side's record before its corpora
/// ran: not after the old compiler has been through every case.
#[test]
fn a_record_that_cannot_be_written_stops_the_run_before_any_case() {
    let world = World::new();
    let keep = world.path("kept").display().to_string();
    let run = world.delta("accept", "squatter", &["--corpora", "sweep", "--keep", &keep]);
    assert_eq!(run.code, 3, "{}", run.text);
    let record = fs::canonicalize(world.path("kept")).unwrap().join("new/record.ndjson");
    assert!(
        run.text.contains(&format!(
            "CORPUS-DELTA: COULD NOT RUN — new: cannot write {}: ",
            record.display()
        )),
        "{}",
        run.text
    );
    assert!(run.specs.is_empty(), "no case may run when a record cannot be written");
    assert!(run.flips().is_empty(), "{}", run.text);
    // The old side's record was opened first, and holds nothing.
    assert_eq!(fs::read_to_string(world.path("kept/old/record.ndjson")).unwrap(), "");
    // The control: the same compiler with nothing in the record's place runs.
    assert_eq!(world.delta("accept", "accept", &["--corpora", "sweep"]).code, 0);
}

#[test]
fn a_cause_is_the_first_error_line_cut_to_160_characters() {
    let world = World::new();
    let keep = world.path("kept").display().to_string();
    world.delta("accept", "long-cause", &["--keep", &keep, "--corpora", "sweep"]);
    let cause = &world.kept("kept", "new")[0].cause;
    assert_eq!(*cause, format!("error: {}", "x".repeat(153)), "a tab is shown as a space");
    assert_eq!(cause.chars().count(), 160);
}

#[test]
fn a_verdict_is_written_as_the_word_the_report_prints() {
    for (verdict, text) in [
        (Verdict::Verifies, "verifies"),
        (Verdict::Refuses, "refuses"),
        (Verdict::Crash(101), "crash:101"),
        (Verdict::Crash(-1), "crash:-1"),
        (Verdict::NotJudged, "not-judged"),
    ] {
        assert_eq!(verdict.to_string(), text);
        assert_eq!(serde_json::to_string(&verdict).unwrap(), format!("\"{text}\""));
        assert_eq!(serde_json::from_str::<Verdict>(&format!("\"{text}\"")).unwrap(), verdict);
    }
    for refused in ["crash", "crash:", "crash:0", "crash:1", "crash:x", "Verifies", ""] {
        assert!(
            serde_json::from_str::<Verdict>(&format!("\"{refused}\"")).is_err(),
            "{refused:?} is no verdict"
        );
    }
    assert_eq!(Verdict::of_exit(0), Verdict::Verifies);
    assert_eq!(Verdict::of_exit(1), Verdict::Refuses);
    assert_eq!(Verdict::of_exit(101), Verdict::Crash(101));
}

// --- sides that measured nothing, or not everything ----------------------------

/// [24]
#[test]
fn a_corpus_that_records_no_case_could_not_run() {
    let world = World::new();
    let run = world.delta("accept", "silent", &["--fail-on-loss", "--corpora", "sweep"]);
    assert_eq!(run.code, 3, "{}", run.text);
    assert!(
        run.has_line("CORPUS-DELTA: COULD NOT RUN — new: corpus sweep recorded no case"),
        "{}",
        run.text
    );
    assert!(run.flips().is_empty(), "{}", run.text);
}

/// [25], as far as it has a native counterpart: the shell delta refused a
/// corpus script that exited above 1; here the unit that can fail to run is
/// one compile.
#[test]
fn a_case_whose_compiler_cannot_be_started_could_not_run_and_is_named() {
    let world = World::new();
    let run = world.delta("accept", "unstartable", &["--fail-on-loss", "--corpora", "sweep"]);
    assert_eq!(run.code, 3, "{}", run.text);
    assert!(
        run.has_line(
            "CORPUS-DELTA: COULD NOT RUN — new: sweep/a: cannot start the compiler: it is gone"
        ),
        "{}",
        run.text
    );
    assert!(run.flips().is_empty(), "{}", run.text);
}

/// [26]
#[test]
fn a_case_declared_twice_is_a_table_error() {
    let twice = TABLE_TEXT.replace(
        "[[not_on_yet]]",
        "[[corpus]]\nid = \"twice\"\nglob = \"corpora/sweep/*.rs\"\nargs = []\n\n\
         [[corpus.case]]\nid = \"b\"\nfile = \"corpora/sweep/b.rs\"\n\n[[not_on_yet]]",
    );
    let world = World::with_table(&twice);
    let run = world.delta("accept", "accept", &["--corpora", "sweep"]);
    assert_eq!(run.code, 2, "{}", run.text);
    assert!(
        run.text.contains("corpus twice: case b is declared twice, so its verdict would be")
            && run.text.contains("tests/corpora.toml"),
        "{}",
        run.text
    );
    assert!(run.specs.is_empty());
}

/// [27], and the two flips that are not counted.
#[test]
fn a_case_the_new_side_stops_recording_is_a_loss() {
    let world = World::new();
    let run = world.delta("accept", "drop-b", &["--fail-on-loss", "--corpora", "sweep"]);
    assert_eq!(run.code, 1, "{}", run.text);
    assert_eq!(run.flips(), ["LOSS  sweep/b: verifies -> not recorded by the new side"]);
    assert!(run.has_line(&row("sweep", (3, 3), (2, 2))), "{}", run.text);

    let appeared = world.delta("drop-b", "accept", &["--fail-on-loss", "--corpora", "sweep"]);
    assert_eq!(appeared.code, 0, "{}", appeared.text);
    assert_eq!(appeared.flips(), ["NEW   sweep/b: verifies (not recorded by the old side)"]);
    assert!(appeared.has_line("seal corpus delta: 0 lost, 0 gained"), "{}", appeared.text);
}

fn record(case: &str, verdict: Verdict, pin: Option<Pin>) -> CaseRecord {
    CaseRecord { corpus: "c".into(), case: case.into(), verdict, cause: String::new(), pin }
}

#[test]
fn a_case_that_was_not_as_pinned_and_is_gone_is_not_a_loss() {
    let old = [
        record("held", Verdict::Refuses, Some(Pin::Refuses)),
        record("missed", Verdict::Verifies, Some(Pin::Refuses)),
        record("crashed", Verdict::Crash(101), None),
    ];
    let comparison = compare_with(&old, &[], rank).unwrap();
    assert_eq!(
        comparison.flip_lines(),
        [
            "GONE  c/crashed: crash:101 -> not recorded by the new side",
            "GONE  c/missed: verifies (pinned refuses) -> not recorded by the new side",
            "LOSS  c/held: refuses (pinned refuses) -> not recorded by the new side",
        ]
    );
    assert_eq!((comparison.losses, comparison.gains), (1, 0));
    let kinds: Vec<FlipKind> = comparison.flips.iter().map(|flip| flip.kind).collect();
    assert_eq!(kinds.iter().filter(|kind| **kind == FlipKind::Gone).count(), 2);
    assert_eq!(comparison.tallies["c"].old_as_pinned, 1);
    assert_eq!(comparison.tallies["c"].old_total, 3);
}

/// A table that gained a pin between two records: both verdicts are ranked
/// against the new side's pin, so a case that verified all along under a new
/// `refuses` pin has not moved.
#[test]
fn both_sides_are_ranked_against_the_new_sides_pin() {
    let old = [record("x", Verdict::Verifies, None), record("y", Verdict::Refuses, None)];
    let new = [
        record("x", Verdict::Verifies, Some(Pin::Refuses)),
        record("y", Verdict::Verifies, Some(Pin::Refuses)),
    ];
    let comparison = compare_with(&old, &new, rank).unwrap();
    assert_eq!(
        comparison.flip_lines(),
        ["LOSS  c/y: refuses -> verifies (pinned refuses): a case pinned refuses now verifies"]
    );
    // The counts use each side's own pin.
    let tally = comparison.tallies["c"];
    assert_eq!((tally.old_as_pinned, tally.new_as_pinned), (1, 0));
}

#[test]
fn a_case_recorded_twice_has_no_verdict() {
    let twice = [record("x", Verdict::Verifies, None), record("x", Verdict::Refuses, None)];
    let error = compare_with(&twice, &[], rank).unwrap_err();
    assert_eq!(error, "old: c/x was recorded twice, so its verdict is ambiguous");
    assert!(compare_with(&[], &twice, rank).unwrap_err().starts_with("new: c/x"));
}

/// Critique 1: a case past `--case-seconds` is not judged, is listed, is never
/// ranked, and the run could not run.
#[test]
fn a_case_past_its_bound_is_not_judged_and_never_ranked() {
    let world = World::new();
    let keep = world.path("kept").display().to_string();
    let run = world.delta(
        "hang-one",
        "refuse-all",
        &["--fail-on-loss", "--case-seconds", "7", "--corpora", "sweep", "--keep", &keep],
    );
    assert_eq!(run.code, 3, "{}", run.text);
    // `--keep` is named by its resolved path (a temporary directory's own path
    // may go through a symlink).
    let log = fs::canonicalize(world.path("kept")).unwrap().join("old/sweep/a.log");
    assert!(
        run.has_line(&format!(
            "NOT JUDGED  old sweep/a: no verdict within 7s (log: {})",
            log.display()
        )),
        "{}",
        run.text
    );
    assert!(
        run.text.contains(
            "CORPUS-DELTA: COULD NOT RUN — the old compiler gave no verdict on 1 case(s) within \
             7s each, so nothing was compared"
        ),
        "{}",
        run.text
    );
    assert!(run.flips().is_empty(), "a case with no verdict is never ranked:\n{}", run.text);
    assert!(!run.text.contains("seal corpus delta:"), "{}", run.text);
    assert!(run.specs.iter().all(|spec| spec.bound == Duration::from_secs(7)));
    assert!(
        run.specs.iter().all(|spec| name(&spec.compiler) == "hang-one"),
        "the new side must not start once the old side has a case with no verdict"
    );
    assert_eq!(world.kept("kept", "old")[0].verdict, Verdict::NotJudged);

    // The same on the new side, where the old side's verdicts would otherwise
    // have made every case a flip.
    let new = world.delta("refuse-all", "hang-one", &["--fail-on-loss", "--corpora", "sweep"]);
    assert_eq!(new.code, 3, "{}", new.text);
    // With no `--keep` the log is gone with the run, so the line names no path.
    assert!(
        new.has_line("NOT JUDGED  new sweep/a: no verdict within 1800s (--keep DIR holds its log)"),
        "{}",
        new.text
    );
    assert!(new.flips().is_empty(), "{}", new.text);
}

#[test]
fn a_compiler_that_hangs_on_every_case_is_stopped_at_the_third() {
    let world = World::new();
    let run = world.delta("hang-all", "accept", &["--corpora", "battery,sweep"]);
    assert_eq!(run.code, 3, "{}", run.text);
    assert_eq!(run.specs.len(), 3, "{}", run.text);
    assert_eq!(run.text.lines().filter(|line| line.starts_with("NOT JUDGED  old ")).count(), 3);
    assert!(run.text.contains("gave no verdict on 3 case(s)"), "{}", run.text);
}

// --- exit precedence: 2 > 3 > 1 > 0 (critique 5) -------------------------------

#[test]
fn a_usage_error_outranks_a_compiler_that_does_not_run() {
    let world = World::new();
    let both = world.delta("accept", "broken", &["--corpora", "nonsense"]);
    assert_eq!(both.code, 2, "{}", both.text);
    // The control: the same compiler alone is COULD NOT RUN.
    assert_eq!(world.delta("accept", "broken", &["--corpora", "sweep"]).code, 3);
    // A --keep directory in use is decided before `-vV` too.
    world.write("kept/earlier.txt", "");
    let keep = world.path("kept").display().to_string();
    let kept = world.delta("accept", "broken", &["--corpora", "sweep", "--keep", &keep]);
    assert_eq!(kept.code, 2, "{}", kept.text);
}

#[test]
fn a_table_error_outranks_a_compiler_that_does_not_run() {
    let world = World::with_table(&TABLE_TEXT.replace("trust.corpora.v1", "trust.corpora.v0"));
    let run = world.delta("accept", "broken", &["--corpora", "sweep"]);
    assert_eq!(run.code, 2, "{}", run.text);
    assert!(run.text.contains("schema is \"trust.corpora.v0\""), "{}", run.text);
}

#[test]
fn could_not_run_outranks_a_loss() {
    let world = World::new();
    let args = ["--fail-on-loss", "--corpora", "sweep"];
    let run = world.delta("accept", "refuse-a-hang-b", &args);
    assert_eq!(run.code, 3, "{}", run.text);
    assert!(run.flips().is_empty(), "{}", run.text);
    // The control: the same refusal with every case judged is the loss.
    assert_eq!(world.delta("accept", "refuse-one", &args).code, 1);
}

#[test]
fn a_loss_exits_1_only_under_fail_on_loss() {
    let world = World::new();
    assert_eq!(world.delta("accept", "refuse-one", &["--corpora", "sweep"]).code, 0);
    assert_eq!(
        world.delta("accept", "refuse-one", &["--corpora", "sweep", "--fail-on-loss"]).code,
        1
    );
    assert_eq!(world.delta("accept", "accept", &["--corpora", "sweep", "--fail-on-loss"]).code, 0);
}

// --- the table -----------------------------------------------------------------

#[test]
fn a_table_that_is_not_exactly_the_schema_is_refused_whole() {
    let edits: &[(&str, &str, &str)] = &[
        ("id = \"sweep\"", "id = \"sweep\"\ncolour = \"red\"", "unknown field `colour`"),
        (
            "file = \"corpora/lean/island.rs\"",
            "file = \"corpora/lean/island.rs\"\nlog = 1",
            "unknown field `log`",
        ),
        (
            "corpora/sweep/*.rs",
            "corpora/none/*.rs",
            "corpus sweep: glob \"corpora/none/*.rs\" matches no file",
        ),
        ("corpora/sweep/*.rs", "../sweep/*.rs", "is not a path inside the checkout"),
        ("corpora/lean/island.rs", "/etc/passwd", "is not a path inside the checkout"),
        (
            "corpora/lean/island.rs",
            "corpora/lean/absent.rs",
            "case island: there is no file corpora/lean/absent.rs",
        ),
        (
            "p07 = \"verifies\"",
            "p99 = \"verifies\"",
            "corpus battery: `pins` names p99, which is not a case",
        ),
        (
            "id = \"lean\"",
            "id = \"lean\"\npins = { island = \"refuses\" }",
            "corpus lean: case island is pinned twice",
        ),
        ("pin = \"refuses\"", "pin = \"maybe\"", "unknown variant `maybe`"),
        ("id = \"battery\"", "id = \"sweep\"", "corpus sweep is declared twice"),
        ("id = \"sweep\"", "id = \"Sweep/1\"", "\"Sweep/1\" is not a corpus id"),
        (
            "id = \"bench\"",
            "id = \"lean\"",
            "not_on_yet: lean is declared twice, or is a corpus of this table",
        ),
        (
            "scripts/daily_driver_bench.sh",
            "scripts/absent.sh",
            "not_on_yet bench: there is no scripts/absent.sh",
        ),
        (
            "args = [\"-Z\", \"trust-verify=off\",",
            "args = [\"--out-dir\", \"x\",",
            "`args` names --out-dir, which the verb sets",
        ),
        ("id = \"island\"", "id = \"../island\"", "\"../island\" is not a case id"),
    ];
    for (from, to, why) in edits {
        assert!(TABLE_TEXT.contains(from), "{from:?} is not in the fixture");
        let world = World::with_table(&TABLE_TEXT.replacen(from, to, 1));
        let error = table::load(world.root.path()).unwrap_err();
        assert!(error.contains(why), "{from:?} -> {to:?}: {error}");
        let run = world.delta("accept", "accept", &[]);
        assert_eq!(run.code, 2, "{from:?} -> {to:?}:\n{}", run.text);
        assert!(run.specs.is_empty());
    }
    let empty = World::with_table("schema = \"trust.corpora.v1\"\n");
    assert_eq!(table::load(empty.root.path()).unwrap_err(), "it holds no [[corpus]]");
    let bare =
        World::with_table("schema = \"trust.corpora.v1\"\n[[corpus]]\nid = \"x\"\nargs = []\n");
    assert!(table::load(bare.root.path()).unwrap_err().contains("neither `glob` nor"));
    // The control: the fixture table itself loads.
    let table = table::load(World::new().root.path()).unwrap();
    assert_eq!(
        table.corpora.iter().map(|corpus| corpus.cases.len()).collect::<Vec<_>>(),
        [3, 4, 1]
    );
}

#[test]
fn a_checkout_without_a_table_is_a_usage_error() {
    let world = World::new();
    fs::remove_file(world.path("tests/corpora.toml")).unwrap();
    let found = world.delta("accept", "accept", &[]);
    assert_eq!(found.code, 2, "{}", found.text);
    assert!(found.text.contains("no tests/corpora.toml in"), "{}", found.text);
    let root = world.root.path().display().to_string();
    let named = world.delta("accept", "accept", &["--repo-root", &root]);
    assert_eq!(named.code, 2, "{}", named.text);
    assert!(named.text.contains("cannot read it"), "{}", named.text);
}

/// This checkout, from the package directory Cargo compiled this test in.
fn checkout() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("targo-trust is in a checkout")
        .to_path_buf()
}

#[test]
fn the_checked_in_table_loads() {
    let table = table::load(&checkout()).unwrap();
    let ids: Vec<&str> = table.corpora.iter().map(|corpus| corpus.id.as_str()).collect();
    assert_eq!(ids, ["sweep", "battery", "idiomatic", "bench", "probes", "ladder"]);
    let absent: Vec<&str> = table.not_on_yet.iter().map(|absent| absent.id.as_str()).collect();
    assert!(absent.is_empty(), "all six daily-driver corpora are rows: {absent:?}");
    // The first three, as they were; `cases` has the three that joined them.
    for corpus in &table.corpora[..3] {
        assert!(!corpus.cases.is_empty());
        for case in &corpus.cases {
            let pin = match (corpus.id.as_str(), case.id.as_str()) {
                ("battery", "p07") => Some(Pin::Verifies),
                ("battery", _) => Some(Pin::Refuses),
                _ => None,
            };
            assert_eq!(case.pin, pin, "{}/{}", corpus.id, case.id);
        }
    }
    assert!(table.corpora[1].cases.iter().any(|case| case.id == "p07"));
}

/// Until a sealed toolchain carries the verb, the three corpora are also the
/// scripts their `slow.*` harness rows run. The table's files, arguments and
/// pins are those scripts' own; this fails when the two part.
#[test]
fn the_table_matches_the_corpus_scripts() {
    let root = checkout();
    let table = table::load(&root).unwrap();
    for (id, script) in [
        ("sweep", "scripts/ordinary_rust_sweep.sh"),
        ("battery", "scripts/panicking_std_battery.sh"),
        ("idiomatic", "scripts/idiomatic_rust_sample.sh"),
    ] {
        let corpus = table.corpora.iter().find(|corpus| corpus.id == id).unwrap();
        let text = fs::read_to_string(root.join(script)).unwrap();
        let directory = corpus.cases[0].source.parent().unwrap();
        let relative = directory.strip_prefix(&root).unwrap().display().to_string();
        let lists = format!("for f in \"$ROOT\"/{relative}/*.rs; do");
        assert!(text.contains(&lists), "{script} no longer has `{lists}`");
        let sources = fs::read_dir(directory)
            .unwrap()
            .filter(|entry| {
                entry
                    .as_ref()
                    .unwrap()
                    .path()
                    .extension()
                    .is_some_and(|extension| extension == "rs")
            })
            .count();
        assert_eq!(corpus.cases.len(), sources, "{id}: one case per .rs file in {relative}");
        for case in &corpus.cases {
            let compiles = format!("\"$TC\" {} --out-dir ", case.args.join(" "));
            assert!(text.contains(&compiles), "{script} no longer has `{compiles}`");
        }
    }
    let battery = fs::read_to_string(root.join("scripts/panicking_std_battery.sh")).unwrap();
    let pins = "if [ \"$n\" = \"p07\" ]; then expect=pass; else expect=fail; fi";
    assert!(battery.contains(pins), "the battery script no longer has `{pins}`");
}
