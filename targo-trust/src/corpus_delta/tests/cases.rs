//! What a row can ask of a case beyond an exit status: a text its output must
//! hold, a `conditional` pin, a dependency built first, an environment
//! variable, an id that is a path, and a row a file states about itself. Each
//! has a control: the same case with the compiler it is pinned to.
//!
//! The last tests tie the three corpora that ask these things (bench, probes,
//! ladder) to the scripts their `slow.*` harness rows still run.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use super::super::cli::{Host, run_with};
use super::super::headers::{self, Dialect};
use super::super::run::{self, CaseExit, CaseRunner, CaseSpec};
use super::super::table::{self, Case, Certify, Corpus, DependencyUse};
use super::super::{CaseRecord, Pin, Verdict, compare_with, rank};
use super::{FakeProbe, Run, World, checkout, executable, name, row};

const DISCLOSURE: &str = "recorded as `assumption:x` (NOT proved)";
const REFUSAL: &str = "certify verification failed";

const TABLE: &str = r#"schema = "trust.corpora.v1"

[[corpus]]
id = "rows"
args = ["--crate-type=lib"]

[corpus.conditional]
disclosure = 'recorded as `assumption:x` (NOT proved)'
certify_args = ["-Zpolicy=certify"]
certify_refusal = "certify verification failed"

[[corpus.case]]
id = "plain"
file = "rows/plain.rs"
pin = "refuses"

[[corpus.case]]
id = "marked"
file = "rows/marked.rs"
pin = "refuses"
log_contains = "the decisive row"

[[corpus.case]]
id = "disclosed"
file = "rows/disclosed.rs"
pin = "verifies"
log_contains = "relative to its writer"

[[corpus.case]]
id = "cond"
file = "rows/cond.rs"
pin = "conditional"

[[corpus]]
id = "ladder"

[corpus.conditional]
disclosure = 'recorded as `assumption:x` (NOT proved)'
certify_args = ["-Zpolicy=certify"]
certify_refusal = "certify verification failed"

[[corpus.group]]
glob = "ladder/*.rs"
args = ["--edition", "2021"]
env = { VANILLA_DEBUG = "1" }
headers = "trust-ladder"

[[corpus.group]]
glob = "ladder/xcrate/user_*.rs"
ids_under = "ladder"
args = ["--edition", "2021"]
headers = "trust-ladder-xcrate"
dependencies = "ladder/xcrate/lib*.rs"
dependency_args = ["--edition", "2021", "--crate-type=lib", "-Zalways-encode-mir"]

[[corpus]]
id = "bench"
pin = "verifies"
pins = { "fmt/m3" = "refuses" }

[[corpus.group]]
glob = "bench/*/*.rs"
ids_under = "bench"
args = ["--edition", "2021", "--crate-type", "lib"]
"#;

/// The fixture's files that state their own rows, and its dependencies.
const HEADED: [(&str, &str); 8] = [
    ("ladder/v1.rs", "//@ trust-ladder: verifies\npub fn f() {}\n"),
    (
        "ladder/r1.rs",
        "//@ trust-ladder: refuses\n//@ trust-ladder-row: <dyn Write>::write_str\n\
         //@ trust-ladder-crate-type: bin\nfn main() {}\n",
    ),
    (
        "ladder/c1.rs",
        "//@ trust-ladder: conditional\n\
         //@ trust-ladder-row: advisory for `c1::f`: 1 instance hypothesis row(s)\n",
    ),
    ("ladder/xcrate/libt.rs", "pub trait T {}\n"),
    ("ladder/xcrate/libs.rs", "//@ trust-ladder-dep-flags: -Zverify=off  -Zextra\n"),
    ("ladder/xcrate/user_ok.rs", "//@ trust-ladder-xcrate: verifies\nfn main() {}\n"),
    ("ladder/xcrate/user_bad.rs", "//@ trust-ladder-xcrate: refuses\nfn main() {}\n"),
    (
        "ladder/xcrate/user_decl.rs",
        "//@ trust-ladder-xcrate: conditional\n//@ trust-ladder-xcrate-dep: libs\n\
         //@ trust-ladder-xcrate-declare: libs\n//@ trust-ladder-crate-type: lib\n",
    ),
];

/// A checkout with the three fixture corpora and the compilers `old` and `new`.
fn world() -> World {
    world_with(TABLE)
}

fn world_with(table: &str) -> World {
    let world = World::with_table(table);
    for case in ["plain", "marked", "disclosed", "cond"] {
        world.write(&format!("rows/{case}.rs"), "pub fn f() {}\n");
    }
    for (path, text) in HEADED {
        world.write(path, text);
    }
    world.write("bench/arith/a1.rs", "pub fn f() {}\n");
    world.write("bench/fmt/m3.rs", "pub fn f() {}\n");
    for compiler in ["old", "new"] {
        world.write(&format!("bin/{compiler}"), "");
        executable(&world.path(&format!("bin/{compiler}")));
    }
    world
}

fn stem(spec: &CaseSpec) -> &str {
    spec.source.file_stem().and_then(|stem| stem.to_str()).expect("a fixture file has a stem")
}

fn is_certify(spec: &CaseSpec) -> bool {
    spec.args.iter().any(|arg| arg == "-Zpolicy=certify")
}

fn is_dependency(spec: &CaseSpec) -> bool {
    spec.args.iter().any(|arg| arg == "-Zalways-encode-mir")
}

/// How a compile ended, and what it printed; `None` when it left no record.
type Outcome = Option<(CaseExit, String)>;

/// The compiler every fixture case is pinned to.
fn model(spec: &CaseSpec) -> Outcome {
    if is_dependency(spec) {
        fs::write(spec.work.join(format!("lib{}.rlib", stem(spec))), "").unwrap();
        return Some((CaseExit::Exited(0), String::new()));
    }
    if is_certify(spec) {
        return Some((CaseExit::Exited(1), format!("error: Trust {REFUSAL}\n")));
    }
    let (code, log) = match stem(spec) {
        "plain" | "user_bad" | "m3" => (1, "error: refused\n".to_owned()),
        "marked" => (1, "error: refused\nnote: the decisive row is this one\n".to_owned()),
        "disclosed" => (0, "note: panic-free relative to its writer\n".to_owned()),
        "cond" | "user_decl" => (0, format!("warning: 1 row {DISCLOSURE}\n")),
        "c1" => (0, "note: advisory for `c1::f`: 1 instance hypothesis row(s)\n".to_owned()),
        "r1" => (1, "error: <dyn Write>::write_str is not panic-free\n".to_owned()),
        _ => (0, String::new()),
    };
    Some((CaseExit::Exited(code), log))
}

/// The model compiler, except that the new side's compile of the file `case`
/// (its certify compile, when `certify`) ends as `exit` and prints `log`.
fn except(
    case: &'static str,
    certify: bool,
    exit: CaseExit,
    log: &'static str,
) -> impl Fn(&CaseSpec) -> Outcome {
    move |spec| {
        if name(&spec.compiler) == "new" && stem(spec) == case && is_certify(spec) == certify {
            Some((exit.clone(), log.to_owned()))
        } else {
            model(spec)
        }
    }
}

struct Scripted<'a> {
    specs: Vec<CaseSpec>,
    act: &'a dyn Fn(&CaseSpec) -> Outcome,
}

impl CaseRunner for Scripted<'_> {
    fn run(&mut self, spec: &CaseSpec) -> Option<CaseExit> {
        self.specs.push(spec.clone());
        let (exit, log) = (self.act)(spec)?;
        fs::write(&spec.log, log).expect("the verb creates the log's directory");
        Some(exit)
    }
}

/// The delta from compiler `old` to compiler `new`, each acting as `act` says.
fn delta(world: &World, act: &dyn Fn(&CaseSpec) -> Outcome, rest: &[&str]) -> Run {
    let args = world.args("old", "new", rest);
    let mut runner = Scripted { specs: Vec::new(), act };
    let mut lines = Vec::new();
    let mut progress = |line: &str| lines.push(line.to_owned());
    let (code, text) = run_with(
        &args,
        &mut Host {
            cwd: world.root.path().to_path_buf(),
            runner: &mut runner,
            probe: &mut FakeProbe,
            progress: &mut progress,
            rank,
        },
    );
    Run { code, text, specs: runner.specs, progress: lines }
}

/// The compiles one side ran, as (case, which compile).
fn compiles<'a>(run: &'a Run, side: &str) -> Vec<(&'a str, &'static str)> {
    run.specs
        .iter()
        .filter(|spec| name(&spec.compiler) == side)
        .map(|spec| {
            let which = if is_dependency(spec) {
                "dependency"
            } else if is_certify(spec) {
                "certify"
            } else {
                "compile"
            };
            (spec.case.as_str(), which)
        })
        .collect()
}

// --- a `conditional` pin --------------------------------------------------------

#[test]
fn a_conditional_case_is_as_pinned_when_certify_refuses_what_its_compile_discloses() {
    let world = world();
    let keep = world.path("kept").display().to_string();
    let run = delta(&world, &model, &["--corpora", "rows", "--keep", &keep, "--fail-on-loss"]);
    assert_eq!(run.code, 0, "{}", run.text);
    assert!(run.flips().is_empty(), "{}", run.text);
    assert!(run.has_line(&row("rows", (4, 4), (4, 4))), "{}", run.text);
    let cond = world.kept("kept", "new").into_iter().find(|record| record.case == "cond");
    assert_eq!(
        cond,
        Some(CaseRecord {
            corpus: "rows".into(),
            case: "cond".into(),
            verdict: Verdict::Conditional,
            cause: String::new(),
            pin: Some(Pin::Conditional),
        })
    );
    // The certify compile: the case's arguments and the corpus's, a directory
    // and a log of its own. Only the conditional case has one.
    let certify: Vec<&CaseSpec> = run.specs.iter().filter(|spec| is_certify(spec)).collect();
    assert_eq!(certify.len(), 2, "one for each side");
    for spec in certify {
        assert_eq!(spec.case, "cond");
        assert_eq!(spec.args, ["--crate-type=lib", "-Zpolicy=certify"]);
        assert!(spec.work.ends_with("rows/cond.certify"), "{}", spec.work.display());
        assert!(spec.log.ends_with("rows/cond.certify.log"), "{}", spec.log.display());
        assert_eq!(spec.source, world.path("rows/cond.rs"));
    }
    assert!(world.path("kept/new/rows/cond.certify.log").is_file());
    assert_eq!(
        compiles(&run, "old"),
        [
            ("plain", "compile"),
            ("marked", "compile"),
            ("disclosed", "compile"),
            ("cond", "compile"),
            ("cond", "certify"),
        ]
    );
}

#[test]
fn a_conditional_case_that_exits_0_without_its_condition_is_ranked_a_false_proof() {
    use CaseExit::{Exited, Signalled};
    let world = world();
    let args = ["--corpora", "rows", "--fail-on-loss"];
    let no_disclosure =
        "exit 0, and its output has no \"recorded as `assumption:x` (NOT proved)\"".to_owned();
    let without = |ended: &str| {
        format!("its certify compile {ended} without \"certify verification failed\"")
    };
    let misses: [(bool, CaseExit, &'static str, String); 4] = [
        (false, Exited(0), "note: nothing is disclosed\n", no_disclosure),
        (true, Exited(0), "", "its certify compile accepts it".to_owned()),
        (
            true,
            Exited(1),
            "error: something else\n",
            format!("{}: error: something else", without("exited 1")),
        ),
        (true, Signalled(9), "", without("was ended by signal 9")),
    ];
    for (certify, exit, log, cause) in misses {
        let run = delta(&world, &except("cond", certify, exit, log), &args);
        assert_eq!(run.code, 1, "{cause}:\n{}", run.text);
        let loss =
            format!("LOSS  rows/cond: conditional -> verifies (pinned conditional): {cause}");
        assert_eq!(run.flips(), [loss.as_str()], "{}", run.text);
        assert!(run.has_line(&row("rows", (4, 4), (3, 4))), "{}", run.text);
        // The certify compile is run exactly when the first half held.
        let ran = compiles(&run, "new").contains(&("cond", "certify"));
        assert_eq!(ran, certify, "{cause}:\n{}", run.text);
    }
    // The control: the same compiler with nothing changed has no flip
    // (`a_conditional_case_is_as_pinned_…`), and neither has a certify compile
    // that refuses with its text under another non-zero status.
    let crashed_refusing =
        except("cond", true, Exited(101), "error: Trust certify verification failed\npanicked\n");
    let run = delta(&world, &crashed_refusing, &args);
    assert_eq!(run.code, 0, "{}", run.text);
    assert!(run.flips().is_empty(), "{}", run.text);
}

#[test]
fn a_conditional_case_that_refuses_is_a_clean_miss_above_one_that_verifies_outright() {
    let world = world();
    let refused = except("cond", false, CaseExit::Exited(1), "error: refused now\n");
    let run = delta(&world, &refused, &["--corpora", "rows", "--fail-on-loss"]);
    assert_eq!(run.code, 1, "{}", run.text);
    assert_eq!(
        run.flips(),
        ["LOSS  rows/cond: conditional -> refuses (pinned conditional): error: refused now"],
        "{}",
        run.text
    );
    assert!(!compiles(&run, "new").contains(&("cond", "certify")), "nothing to certify");

    let pin = Some(Pin::Conditional);
    let record = |verdict, cause: &str| CaseRecord {
        corpus: "c".into(),
        case: "x".into(),
        verdict,
        cause: cause.into(),
        pin,
    };
    let refuses = [record(Verdict::Refuses, "error: refused")];
    let outright = [record(Verdict::Verifies, "its certify compile accepts it")];
    let conditional = [record(Verdict::Conditional, "")];
    let down = compare_with(&refuses, &outright, rank).unwrap();
    assert_eq!(
        down.flip_lines(),
        ["LOSS  c/x: refuses -> verifies (pinned conditional): its certify compile accepts it"]
    );
    let up = compare_with(&outright, &conditional, rank).unwrap();
    assert_eq!(
        up.flip_lines(),
        ["GAIN  c/x: verifies -> conditional (pinned conditional) (was: its certify compile \
          accepts it)"]
    );
    assert_eq!((up.tallies["c"].old_as_pinned, up.tallies["c"].new_as_pinned), (0, 1));
    // A record that names no cause still says what the loss is.
    let silent = compare_with(&conditional, &[record(Verdict::Verifies, "")], rank).unwrap();
    assert_eq!(
        silent.flip_lines(),
        ["LOSS  c/x: conditional -> verifies (pinned conditional): a case pinned conditional now \
          verifies without its condition"]
    );
}

#[test]
fn a_certify_compile_past_its_bound_or_unrecorded_gives_its_case_no_verdict() {
    let world = world();
    let args = ["--corpora", "rows", "--fail-on-loss"];
    let hung = delta(&world, &except("cond", true, CaseExit::PastBound, ""), &args);
    assert_eq!(hung.code, 3, "{}", hung.text);
    assert!(
        hung.has_line(
            "NOT JUDGED  new rows/cond: no verdict within 1800s (--keep DIR holds its log)"
        ),
        "{}",
        hung.text
    );
    assert!(hung.flips().is_empty(), "{}", hung.text);

    let failed = except("cond", true, CaseExit::Failed("cannot start it".into()), "");
    let failed = delta(&world, &failed, &args);
    assert_eq!(failed.code, 3, "{}", failed.text);
    assert!(
        failed.has_line("CORPUS-DELTA: COULD NOT RUN — new: rows/cond: cannot start it"),
        "{}",
        failed.text
    );

    let unrecorded = |spec: &CaseSpec| {
        if name(&spec.compiler) == "new" && is_certify(spec) { None } else { model(spec) }
    };
    let run = delta(&world, &unrecorded, &args);
    assert_eq!(run.code, 1, "{}", run.text);
    assert_eq!(
        run.flips(),
        ["LOSS  rows/cond: conditional (pinned conditional) -> not recorded by the new side"],
        "{}",
        run.text
    );
}

// --- a text the output must hold -------------------------------------------------

#[test]
fn a_pinned_exit_without_its_text_is_not_as_pinned() {
    let world = world();
    let args = ["--corpora", "rows", "--fail-on-loss"];
    // `plain` is the control: it prints what `marked` prints here, is pinned
    // the same, names no text, and stays as pinned.
    let elsewhere = except("marked", false, CaseExit::Exited(1), "error: refused\n");
    let run = delta(&world, &elsewhere, &args);
    assert_eq!(run.code, 1, "{}", run.text);
    assert_eq!(
        run.flips(),
        ["LOSS  rows/marked: refuses -> refuses-otherwise (pinned refuses): its output has no \
          \"the decisive row\""],
        "{}",
        run.text
    );
    assert!(run.has_line(&row("rows", (4, 4), (3, 4))), "{}", run.text);

    let undisclosed = except("disclosed", false, CaseExit::Exited(0), "");
    let run = delta(&world, &undisclosed, &args);
    assert_eq!(
        run.flips(),
        ["LOSS  rows/disclosed: verifies -> verifies-otherwise (pinned verifies): its output has \
          no \"relative to its writer\""],
        "{}",
        run.text
    );

    // A text that is split over two lines is not there.
    let split = except("marked", false, CaseExit::Exited(1), "error: the decisive\n row\n");
    assert_eq!(delta(&world, &split, &args).flips().len(), 1);
}

#[test]
fn a_text_is_looked_for_only_under_the_pinned_exit() {
    let world = world();
    let args = ["--corpora", "rows", "--fail-on-loss"];
    // Verifying a case pinned `refuses` is the false proof, text or no text.
    let verified = except("marked", false, CaseExit::Exited(0), "note: the decisive row\n");
    let run = delta(&world, &verified, &args);
    assert_eq!(
        run.flips(),
        ["LOSS  rows/marked: refuses -> verifies (pinned refuses): a case pinned refuses now \
          verifies"],
        "{}",
        run.text
    );
    let refused = except("disclosed", false, CaseExit::Exited(1), "error: no longer verifies\n");
    let run = delta(&world, &refused, &args);
    assert_eq!(
        run.flips(),
        ["LOSS  rows/disclosed: verifies -> refuses (pinned verifies): error: no longer verifies"],
        "{}",
        run.text
    );
    let crashed = except("marked", false, CaseExit::Exited(101), "error: the decisive row\n");
    let run = delta(&world, &crashed, &args);
    assert_eq!(
        run.flips(),
        ["LOSS  rows/marked: refuses -> crash:101 (pinned refuses): error: the decisive row"],
        "{}",
        run.text
    );
}

#[test]
fn a_text_is_found_on_one_line_anywhere_in_a_log() {
    let directory = tempfile::tempdir().unwrap();
    let log = directory.path().join("case.log");
    let filler = "note: a line that is not the one\n".repeat(200_000);
    fs::write(&log, format!("{filler}warning: here is the needle, far down\n")).unwrap();
    assert!(fs::metadata(&log).unwrap().len() > 6_000_000);
    assert!(run::log_contains(&log, "is the needle, far").unwrap());
    assert!(!run::log_contains(&log, "the needle is here").unwrap());
    assert!(!run::log_contains(&log, "one\nnote").unwrap(), "a text is on one line");
    fs::write(&log, b"\xff\xfe not UTF-8, and the needle\n").unwrap();
    assert!(run::log_contains(&log, "the needle").unwrap());
    assert!(run::log_contains(&directory.path().join("absent.log"), "x").is_err());
}

// --- rows files state about themselves, and their dependencies -------------------

fn corpus<'a>(table: &'a table::Table, id: &str) -> &'a Corpus {
    table.corpora.iter().find(|corpus| corpus.id == id).expect("the corpus is in the table")
}

fn case<'a>(corpus: &'a Corpus, id: &str) -> &'a Case {
    corpus.cases.iter().find(|case| case.id == id).expect("the case is in the corpus")
}

fn strings(words: &[&str]) -> Vec<String> {
    words.iter().map(|word| (*word).to_owned()).collect()
}

#[test]
fn a_headed_group_reads_each_row_from_its_file() {
    let world = world();
    let table = table::load(world.root.path()).unwrap();
    let ladder = corpus(&table, "ladder");
    let ids: Vec<&str> = ladder.cases.iter().map(|case| case.id.as_str()).collect();
    assert_eq!(ids, ["c1", "r1", "v1", "xcrate/user_bad", "xcrate/user_decl", "xcrate/user_ok"]);
    let debug = vec![("VANILLA_DEBUG".to_owned(), "1".to_owned())];
    let certify =
        Some(Certify { args: strings(&["-Zpolicy=certify"]), refusal: REFUSAL.to_owned() });

    let v1 = case(ladder, "v1");
    assert_eq!(v1.pin, Some(Pin::Verifies));
    assert_eq!(v1.args, ["--edition", "2021", "--crate-type=lib"], "a library unless `bin`");
    assert_eq!(v1.env, debug);
    assert_eq!((&v1.log_contains, &v1.certify, &v1.dependency), (&None, &None, &None));

    let r1 = case(ladder, "r1");
    assert_eq!(r1.pin, Some(Pin::Refuses));
    assert_eq!(r1.args, ["--edition", "2021"], "`bin` is no crate type");
    assert_eq!(r1.log_contains.as_deref(), Some("<dyn Write>::write_str"));

    let c1 = case(ladder, "c1");
    assert_eq!(c1.pin, Some(Pin::Conditional));
    assert_eq!(
        c1.log_contains.as_deref(),
        Some("advisory for `c1::f`: 1 instance hypothesis row(s)"),
        "its own text, not the corpus's disclosure"
    );
    assert_eq!(c1.certify, certify);

    let ok = case(ladder, "xcrate/user_ok");
    assert_eq!(ok.args, ["--edition", "2021"], "a binary unless `lib`");
    assert!(ok.env.is_empty(), "the group names no variable");
    assert_eq!(
        ok.dependency,
        Some(DependencyUse { name: "libt".into(), then_args: Vec::new() }),
        "`libt` where the row names none"
    );
    let declared = case(ladder, "xcrate/user_decl");
    assert_eq!(declared.args, ["--edition", "2021", "--crate-type=lib"]);
    assert_eq!(
        declared.dependency,
        Some(DependencyUse {
            name: "libs".into(),
            then_args: strings(&["-Ztrust-bundle-foreign-crate=libs"]),
        })
    );
    assert_eq!(declared.log_contains.as_deref(), Some(DISCLOSURE), "the corpus's, having none");
    assert_eq!(declared.certify, certify);

    let built: Vec<(&str, &str, Vec<&str>)> = ladder
        .dependencies
        .iter()
        .map(|dependency| {
            (
                dependency.id.as_str(),
                dependency.name.as_str(),
                dependency.args.iter().map(String::as_str).collect(),
            )
        })
        .collect();
    let base = ["--edition", "2021", "--crate-type=lib", "-Zalways-encode-mir"];
    assert_eq!(
        built,
        [
            ("xcrate/libs", "libs", [&base[..], &["-Zverify=off", "-Zextra"][..]].concat()),
            ("xcrate/libt", "libt", base.to_vec()),
        ]
    );

    // A group with `ids_under` names a case by its path; the corpus's `pins`
    // reach it by that name.
    let bench = corpus(&table, "bench");
    let pins: Vec<(&str, Option<Pin>)> =
        bench.cases.iter().map(|case| (case.id.as_str(), case.pin)).collect();
    assert_eq!(pins, [("arith/a1", Some(Pin::Verifies)), ("fmt/m3", Some(Pin::Refuses))]);
    assert_eq!(case(bench, "fmt/m3").source, world.path("bench/fmt/m3.rs"));
    assert!(bench.dependencies.is_empty());
}

#[test]
fn a_dependency_is_built_once_for_a_side_before_its_first_case() {
    let world = world();
    let keep = world.path("kept").display().to_string();
    let run = delta(&world, &model, &["--corpora", "ladder,bench", "--keep", &keep]);
    assert_eq!(run.code, 0, "{}", run.text);
    assert!(run.flips().is_empty(), "{}", run.text);
    assert!(run.has_line(&row("ladder", (6, 6), (6, 6))), "{}", run.text);
    assert!(run.has_line(&row("bench", (2, 2), (2, 2))), "{}", run.text);
    assert!(run.progress.contains(&"corpus-delta: old: ladder (6 case(s))".to_owned()));
    let ladder: Vec<(&str, &str)> =
        compiles(&run, "new").into_iter().filter(|(case, _)| !case.contains("/m")).collect();
    assert_eq!(
        ladder,
        [
            ("c1", "compile"),
            ("c1", "certify"),
            ("r1", "compile"),
            ("v1", "compile"),
            ("xcrate/libt", "dependency"),
            ("xcrate/user_bad", "compile"),
            ("xcrate/libs", "dependency"),
            ("xcrate/user_decl", "compile"),
            ("xcrate/user_decl", "certify"),
            ("xcrate/user_ok", "compile"),
            ("arith/a1", "compile"),
        ],
        "libt is built once, for user_bad, and user_ok uses it"
    );

    let new = |case: &str, which: &str| {
        run.specs
            .iter()
            .filter(|spec| name(&spec.compiler) == "new" && spec.case == case)
            .find(|spec| match which {
                "certify" => is_certify(spec),
                _ => !is_certify(spec),
            })
            .unwrap_or_else(|| panic!("the new side ran no {which} of {case}"))
    };
    let work = &new("v1", "compile").work;
    assert!(work.ends_with("new/ladder"), "{}", work.display());
    let libt = work.join("xcrate/libt.dependency");
    let libs = work.join("xcrate/libs.dependency");

    // A dependency: its own arguments, directory and log, and no variable.
    let dependency = new("xcrate/libs", "compile");
    assert_eq!(dependency.work, libs);
    assert_eq!(dependency.source, world.path("ladder/xcrate/libs.rs"));
    assert!(dependency.log.ends_with("new/ladder/xcrate/libs.dependency.log"));
    assert!(dependency.env.is_empty());
    assert!(world.path("kept/new/ladder/xcrate/libs.dependency.log").is_file());

    // A row built against one: `--extern` and `-L` after its own arguments,
    // then what its headers add.
    let bad = new("xcrate/user_bad", "compile");
    let liblibt = format!("libt={}", libt.join("liblibt.rlib").display());
    assert_eq!(
        bad.args,
        ["--edition", "2021", "--extern", liblibt.as_str(), "-L", libt.to_str().unwrap()]
    );
    assert_eq!(&bad.work, work, "a case's compile shares its corpus's directory");
    let liblibs = format!("libs={}", libs.join("liblibs.rlib").display());
    let declared = [
        "--edition",
        "2021",
        "--crate-type=lib",
        "--extern",
        liblibs.as_str(),
        "-L",
        libs.to_str().unwrap(),
        "-Ztrust-bundle-foreign-crate=libs",
    ];
    assert_eq!(new("xcrate/user_decl", "compile").args, declared);
    assert_eq!(
        new("xcrate/user_decl", "certify").args,
        [&declared[..], &["-Zpolicy=certify"][..]].concat()
    );

    // The group's variable reaches a case's compile and not its certify
    // compile; the other group has none.
    let debug = vec![("VANILLA_DEBUG".to_owned(), "1".to_owned())];
    assert_eq!(new("c1", "compile").env, debug);
    assert!(new("c1", "certify").env.is_empty());
    assert!(bad.env.is_empty());

    // A case whose id is a path logs under it.
    assert!(world.path("kept/new/bench/arith/a1.log").is_file());
    assert!(world.path("kept/new/ladder/xcrate/user_ok.log").is_file());
    let kept = world.kept("kept", "new");
    assert_eq!(kept.len(), 8, "a dependency has no record");
    assert!(kept.iter().all(|record| !record.case.contains("lib")));
}

#[test]
fn a_dependency_that_does_not_build_blocks_each_of_its_cases_whatever_its_pin() {
    let world = world();
    let args = ["--corpora", "ladder", "--fail-on-loss"];
    let run =
        delta(&world, &except("libt", false, CaseExit::Exited(1), "error: dep broke\n"), &args);
    assert_eq!(run.code, 1, "{}", run.text);
    // `user_bad` is pinned `refuses`: a dependency that refused is not its
    // refusal. The control is the run where libt builds (the test above), in
    // which the same row is as pinned.
    assert_eq!(
        run.flips(),
        [
            "LOSS  ladder/xcrate/user_bad: refuses -> blocked (pinned refuses): its dependency \
             xcrate/libt did not build: error: dep broke",
            "LOSS  ladder/xcrate/user_ok: verifies -> blocked (pinned verifies): its dependency \
             xcrate/libt did not build: error: dep broke",
        ],
        "{}",
        run.text
    );
    assert!(run.has_line(&row("ladder", (6, 6), (4, 6))), "{}", run.text);
    let new = compiles(&run, "new");
    assert_eq!(new.iter().filter(|compile| **compile == ("xcrate/libt", "dependency")).count(), 1);
    assert!(!new.contains(&("xcrate/user_bad", "compile")), "a blocked case is not compiled");
    assert!(new.contains(&("xcrate/user_decl", "compile")), "libs built, so its row ran");

    // Exit 0 with no rlib is no dependency either.
    let empty = delta(&world, &except("libt", false, CaseExit::Exited(0), ""), &args);
    assert!(
        empty.has_line(
            "LOSS  ladder/xcrate/user_ok: verifies -> blocked (pinned verifies): its dependency \
             xcrate/libt exited 0 and left no liblibt.rlib"
        ),
        "{}",
        empty.text
    );

    // A dependency the compiler crashes on is a crash of each of its cases.
    let crashed = except("libt", false, CaseExit::Exited(101), "error: internal compiler error\n");
    let crashed = delta(&world, &crashed, &args);
    assert!(
        crashed.has_line(
            "LOSS  ladder/xcrate/user_bad: refuses -> crash:101 (pinned refuses): its dependency \
             xcrate/libt: error: internal compiler error"
        ),
        "{}",
        crashed.text
    );
    assert!(crashed.has_line("the new compiler crashed on 2 case(s)"), "{}", crashed.text);
}

#[test]
fn a_dependency_with_no_exit_gives_its_cases_no_verdict() {
    let world = world();
    let args = ["--corpora", "ladder", "--fail-on-loss"];
    let hung = delta(&world, &except("libt", false, CaseExit::PastBound, ""), &args);
    assert_eq!(hung.code, 3, "{}", hung.text);
    for case in ["user_bad", "user_ok"] {
        assert!(
            hung.has_line(&format!(
                "NOT JUDGED  new ladder/xcrate/{case}: its dependency xcrate/libt: no verdict \
                 within 1800s (--keep DIR holds its log)"
            )),
            "{}",
            hung.text
        );
    }
    assert!(hung.flips().is_empty(), "{}", hung.text);

    let failed = except("libt", false, CaseExit::Failed("cannot start it".into()), "");
    let failed = delta(&world, &failed, &args);
    assert_eq!(failed.code, 3, "{}", failed.text);
    assert!(
        failed.has_line("CORPUS-DELTA: COULD NOT RUN — new: ladder/xcrate/libt: cannot start it"),
        "{}",
        failed.text
    );

    let unrecorded = |spec: &CaseSpec| {
        if name(&spec.compiler) == "new" && stem(spec) == "libt" { None } else { model(spec) }
    };
    let run = delta(&world, &unrecorded, &args);
    assert_eq!(
        run.flips(),
        [
            "LOSS  ladder/xcrate/user_bad: refuses (pinned refuses) -> not recorded by the new \
             side",
            "LOSS  ladder/xcrate/user_ok: verifies (pinned verifies) -> not recorded by the new \
             side",
        ],
        "{}",
        run.text
    );
}

#[test]
fn a_header_is_the_first_line_of_its_name_and_the_rest_of_that_line() {
    let ladder = |text: &str| headers::row(Dialect::Ladder, text);
    let row = ladder(
        "// a comment\n//@ trust-ladder:   refuses\n//@ trust-ladder: verifies\n\
         //@ trust-ladder-row:  a  b \n//@ trust-ladder-row: later\n",
    )
    .unwrap();
    assert_eq!(row.pin, Pin::Refuses, "the first line of a name counts");
    assert_eq!(row.log_contains.as_deref(), Some("a  b "), "leading spaces only are dropped");
    assert_eq!(row.args, ["--crate-type=lib"]);
    assert_eq!(row.dependency, None);
    let none = "it has no `//@ trust-ladder:` line, so it states no row";
    for text in [
        "",
        "  //@ trust-ladder: verifies\n",
        "//@trust-ladder: verifies\n",
        "//@ trust-ladder-row: verifies\n",
        "//@ trust-ladder-xcrate: verifies\n",
        // A first line with no value says nothing, whatever a later one says.
        "//@ trust-ladder:\n//@ trust-ladder: verifies\n",
    ] {
        assert_eq!(ladder(text).unwrap_err(), none, "{text:?}");
    }
    let unmarked = ladder(
        "//@ trust-ladder: verifies\n//@ trust-ladder-row:  \n//@ trust-ladder-row: later\n",
    );
    assert_eq!(unmarked.unwrap().log_contains, None);
    assert_eq!(ladder("//@ trust-ladder: conditional").unwrap().pin, Pin::Conditional);

    let xcrate = |text: &str| headers::row(Dialect::LadderXcrate, text).unwrap();
    let plain = xcrate("//@ trust-ladder-xcrate: conditional\n");
    assert_eq!((plain.pin, plain.args.len()), (Pin::Conditional, 0));
    assert_eq!(plain.dependency, Some(("libt".to_owned(), Vec::new())));
    let declared = xcrate(
        "//@ trust-ladder-xcrate: refuses\n//@ trust-ladder-xcrate-dep: libgen\n\
         //@ trust-ladder-xcrate-declare: libgen\n//@ trust-ladder-crate-type: lib\n",
    );
    assert_eq!(declared.args, ["--crate-type=lib"]);
    assert_eq!(
        declared.dependency,
        Some(("libgen".to_owned(), strings(&["-Ztrust-bundle-foreign-crate=libgen"])))
    );

    assert_eq!(
        headers::dependency_flags("//@ trust-ladder-dep-flags: -Za=b   -Zc\n"),
        ["-Za=b", "-Zc"]
    );
    assert!(headers::dependency_flags("pub trait T {}\n").is_empty());
}

// --- the table's refusals --------------------------------------------------------

#[test]
fn a_table_that_asks_what_the_verb_cannot_answer_is_refused_whole() {
    let block = "\n[corpus.conditional]\ndisclosure = 'recorded as `assumption:x` (NOT proved)'\n\
                 certify_args = [\"-Zpolicy=certify\"]\ncertify_refusal = \"certify verification \
                 failed\"\n";
    let bench_pins = "pins = { \"fmt/m3\" = \"refuses\" }\n";
    let with_block = format!("{bench_pins}{block}");
    let xcrate_arguments = "dependency_args = [\"--edition\", \"2021\", \"--crate-type=lib\", \
                            \"-Zalways-encode-mir\"]\n";
    // One byte more than a text may be; `at_the_bound` below is its control.
    let over_the_bound = format!("log_contains = \"{}\"", "x".repeat(513));
    // Two groups with their own rows that build the same crates.
    let two_groups = "glob = \"ladder/xcrate/user_ok.rs\"\nids_under = \"ladder\"\n\
                      args = [\"--edition\", \"2021\"]\nheaders = \"trust-ladder-xcrate\"\n\
                      dependencies = \"ladder/xcrate/lib*.rs\"\ndependency_args = []\n\n\
                      [[corpus.group]]\nglob = \"ladder/xcrate/user_[bd]*.rs\"\n";
    let disclosure = "disclosure = 'recorded as `assumption:x` (NOT proved)'";
    let edits: &[(&str, &str, &str)] = &[
        (
            "env = { VANILLA_DEBUG = \"1\" }",
            "env = { VANILLA_DEBUG = \"1\" }\ncolour = \"red\"",
            "unknown field `colour`",
        ),
        (
            "headers = \"trust-ladder\"\n",
            "headers = \"trust-ladders\"\n",
            "unknown variant `trust-ladders`",
        ),
        (
            block,
            "\n",
            "corpus rows: case cond is pinned conditional, and the corpus has no \
             [corpus.conditional]",
        ),
        (
            bench_pins,
            &with_block,
            "corpus bench: it has a [corpus.conditional] and no case pinned conditional",
        ),
        (
            "certify_args = [\"-Zpolicy=certify\"]",
            "certify_args = []",
            "corpus rows: [corpus.conditional] certify_args is empty",
        ),
        (
            "certify_refusal = \"certify verification failed\"",
            "certify_refusal = \"\"",
            "[corpus.conditional] certify_refusal: the text its output must hold is empty",
        ),
        (
            "pin = \"verifies\"\nlog_contains = \"relative to its writer\"",
            "log_contains = \"relative to its writer\"",
            "corpus rows: case disclosed has `log_contains` and no pin",
        ),
        (
            "log_contains = \"the decisive row\"",
            "log_contains = \"\"",
            "case marked: the text its output must hold is empty",
        ),
        (
            "log_contains = \"the decisive row\"",
            "log_contains = \"the decisive\\nrow\"",
            "case marked: the text its output must hold spans a line",
        ),
        (
            "log_contains = \"the decisive row\"",
            &over_the_bound,
            "case marked: the text its output must hold is over 512 bytes",
        ),
        (
            disclosure,
            "disclosure = ''",
            "corpus rows: [corpus.conditional] disclosure: the text its output must hold is empty",
        ),
        (
            disclosure,
            "disclosure = \"recorded as\\nan assumption\"",
            "corpus rows: [corpus.conditional] disclosure: the text its output must hold spans a \
             line",
        ),
        (
            "certify_args = [\"-Zpolicy=certify\"]",
            "certify_args = [\"-Zpolicy=certify\", \"--out-dir=x\"]",
            "corpus rows: [corpus.conditional]: `args` names --out-dir, which the verb sets",
        ),
        (
            xcrate_arguments,
            "dependency_args = [\"--out-dir\", \"x\"]\n",
            "`dependency_args`: `args` names --out-dir, which the verb sets",
        ),
        (
            "glob = \"ladder/xcrate/user_*.rs\"\n",
            two_groups,
            "corpus ladder: group \"ladder/xcrate/user_[bd]*.rs\": dependency libs is declared \
             twice",
        ),
        (
            "env = { VANILLA_DEBUG = \"1\" }",
            "env = { TRUST_MEMORY_JOBSERVER_SOCK = \"/tmp/sock\" }",
            "`env` names TRUST_MEMORY_JOBSERVER_SOCK, which the verb removes from every compile",
        ),
        (
            "env = { VANILLA_DEBUG = \"1\" }",
            "env = { \"A=B\" = \"1\" }",
            "`env`: \"A=B\" is not a variable a process can be given",
        ),
        (
            "env = { VANILLA_DEBUG = \"1\" }",
            "env = { \"\" = \"1\" }",
            "`env`: \"\" is not a variable a process can be given",
        ),
        (
            "env = { VANILLA_DEBUG = \"1\" }",
            "env = { \"A\\u0000B\" = \"1\" }",
            "`env`: \"A\\0B\" is not a variable a process can be given",
        ),
        (
            "env = { VANILLA_DEBUG = \"1\" }",
            "env = { VANILLA_DEBUG = \"1\\u0000\" }",
            "`env`: \"VANILLA_DEBUG\" is not a variable a process can be given",
        ),
        (
            "headers = \"trust-ladder\"\n",
            "headers = \"trust-ladder\"\ndependencies = \"ladder/xcrate/lib*.rs\"\n\
             dependency_args = []\n",
            "`dependencies` and `dependency_args` go with `headers = \"trust-ladder-xcrate\"`",
        ),
        (
            xcrate_arguments,
            "",
            "`dependencies` and `dependency_args` go with `headers = \"trust-ladder-xcrate\"`",
        ),
        (
            "ids_under = \"ladder\"",
            "ids_under = \"bench\"",
            "libs.rs names no case id under `ids_under`",
        ),
        (
            "ids_under = \"ladder\"",
            "ids_under = \"../ladder\"",
            "`ids_under`: \"../ladder\" is not a path inside the checkout",
        ),
        (
            "id = \"ladder\"\n",
            "id = \"ladder\"\npins = { v1 = \"refuses\" }\n",
            "corpus ladder: case v1 is pinned twice",
        ),
        (
            "id = \"rows\"\nargs = [\"--crate-type=lib\"]\n",
            "id = \"rows\"\n",
            "corpus rows: case plain: it has no `args`, and neither has its corpus",
        ),
        (
            "id = \"bench\"\n",
            "id = \"bench\"\nglob = \"bench/arith/*.rs\"\n",
            "corpus bench: `glob` needs `args`",
        ),
        (
            "glob = \"bench/*/*.rs\"",
            "glob = \"bench/none/*.rs\"",
            "corpus bench: group \"bench/none/*.rs\": glob \"bench/none/*.rs\" matches no file",
        ),
        (
            "[[corpus]]\nid = \"bench\"",
            "[[corpus.group]]\nglob = \"ladder/*.rs\"\nargs = []\n\n[[corpus]]\nid = \"bench\"",
            "corpus ladder: case c1 is declared twice",
        ),
        (
            "args = [\"--edition\", \"2021\", \"--crate-type\", \"lib\"]",
            "args = [\"--out-dir=x\"]",
            "`args` names --out-dir, which the verb sets",
        ),
    ];
    for (from, to, why) in edits {
        assert!(TABLE.contains(from), "{from:?} is not in the fixture");
        let world = world_with(&TABLE.replacen(from, to, 1));
        let error = table::load(world.root.path()).unwrap_err();
        assert!(error.contains(why), "{from:?} -> {to:?}: {error}");
        let run = delta(&world, &model, &[]);
        assert_eq!(run.code, 2, "{from:?} -> {to:?}:\n{}", run.text);
        assert!(run.specs.is_empty());
    }

    // The control of `over_the_bound`: the longest text a row may ask for.
    let at_the_bound = format!("log_contains = \"{}\"", "x".repeat(512));
    let bounded =
        world_with(&TABLE.replacen("log_contains = \"the decisive row\"", &at_the_bound, 1));
    let rows = table::load(bounded.root.path()).unwrap();
    assert_eq!(case(corpus(&rows, "rows"), "marked").log_contains, Some("x".repeat(512)));

    // What a file says of its own row.
    let long_row =
        format!("//@ trust-ladder: refuses\n//@ trust-ladder-row: {}\n", "x".repeat(513));
    let too_large = format!("//@ trust-ladder: verifies\n//{}\n", "/".repeat(1 << 20));
    let files: &[(&str, &str, &str)] = &[
        (
            "ladder/v1.rs",
            "//@ trust-ladder: maybe\n",
            "group \"ladder/*.rs\": case v1: `//@ trust-ladder: maybe` is not `verifies`, \
             `refuses` or `conditional`",
        ),
        (
            "ladder/v1.rs",
            "pub fn f() {}\n",
            "case v1: it has no `//@ trust-ladder:` line, so it states no row",
        ),
        (
            "ladder/v1.rs",
            "//@ trust-ladder: verifies\n//@ trust-ladder-crate-type: rlib\n",
            "case v1: `//@ trust-ladder-crate-type: rlib` is neither `bin` nor `lib`",
        ),
        (
            "ladder/v1.rs",
            "//@ trust-ladder: verifies\n//@ trust-ladder-xcrate-dep: libt\n",
            "case v1: `//@ trust-ladder-xcrate-dep:` belongs to a `trust-ladder-xcrate` row",
        ),
        (
            "ladder/v1.rs",
            "//@ trust-ladder: verifies\n//@ trust-ladder-xcrate-declare: libt\n",
            "case v1: `//@ trust-ladder-xcrate-declare:` belongs to a `trust-ladder-xcrate` row",
        ),
        ("ladder/v1.rs", &long_row, "case v1: the text its output must hold is over 512 bytes"),
        ("ladder/v1.rs", &too_large, "case v1: cannot read its headers: "),
        (
            "ladder/xcrate/libt.rs",
            &too_large,
            "group \"ladder/xcrate/user_*.rs\": case xcrate/libt: cannot read its headers: ",
        ),
        (
            "ladder/xcrate/user_ok.rs",
            "//@ trust-ladder-xcrate: verifies\n//@ trust-ladder-xcrate-dep: libq\n",
            "case xcrate/user_ok: it is built against libq, and `dependencies` matches no libq.rs",
        ),
        (
            "ladder/xcrate/libz.rs",
            "pub trait Z {}\n",
            "corpus ladder: dependency xcrate/libz is built for no case",
        ),
        (
            "ladder/xcrate/libt.rs",
            "//@ trust-ladder-dep-flags: --out-dir=elsewhere\n",
            "dependency xcrate/libt: `args` names --out-dir, which the verb sets",
        ),
    ];
    for (path, text, why) in files {
        let world = world();
        world.write(path, text);
        let error = table::load(world.root.path()).unwrap_err();
        let shown = &text[..text.len().min(80)];
        assert!(error.contains(why), "{path} = {shown:?}: {error}");
        assert_eq!(delta(&world, &model, &[]).code, 2, "{path} = {shown:?}");
    }
    // A file that is not text states no row either.
    let binary = world();
    fs::write(binary.path("ladder/v1.rs"), b"//@ trust-ladder: verifies\n\xff\n").unwrap();
    let error = table::load(binary.root.path()).unwrap_err();
    assert!(error.contains("case v1: cannot read its headers: "), "{error}");
    // The control: the fixture itself loads.
    let table = table::load(world().root.path()).unwrap();
    assert_eq!(
        table.corpora.iter().map(|corpus| corpus.cases.len()).collect::<Vec<_>>(),
        [4, 6, 2]
    );
}

// --- the rank, and the words -----------------------------------------------------

#[test]
fn rank_of_what_a_row_can_ask() {
    use Verdict::{
        Blocked, Conditional, Crash, NotJudged, Refuses, RefusesOtherwise, Verifies,
        VerifiesOtherwise,
    };
    let (verifies, refuses, conditional) =
        (Some(Pin::Verifies), Some(Pin::Refuses), Some(Pin::Conditional));
    // A `conditional` pin: the condition, then a refusal, a crash, an exit 0
    // that shows no condition.
    assert_eq!(rank(Conditional, conditional), Some(2));
    assert_eq!(rank(Refuses, conditional), Some(1));
    assert_eq!(rank(Crash(101), conditional), Some(0));
    assert_eq!(rank(Verifies, conditional), Some(-1));
    assert_eq!(rank(NotJudged, conditional), None);
    // The pinned exit without its text is a miss, never as pinned.
    assert_eq!(rank(VerifiesOtherwise, verifies), Some(1));
    assert_eq!(rank(RefusesOtherwise, refuses), Some(1));
    // A dependency that refused is no verdict of the case: a miss under every
    // pin, a pinned refusal included.
    for pin in [None, verifies, refuses, conditional] {
        assert_eq!(rank(Blocked, pin), Some(1));
        assert_eq!(rank(RefusesOtherwise, pin), Some(1));
    }
    // A verdict another pin produced is ranked as the exit it was.
    assert_eq!(rank(Conditional, verifies), Some(2));
    assert_eq!(rank(Conditional, None), Some(2));
    assert_eq!(rank(Conditional, refuses), Some(-1));
    assert_eq!(rank(VerifiesOtherwise, refuses), Some(-1));
    assert_eq!(rank(VerifiesOtherwise, conditional), Some(-1));
    assert_eq!(rank(VerifiesOtherwise, None), Some(1));
}

#[test]
fn the_verdicts_and_the_pin_a_row_can_ask_for_are_written_as_words() {
    for (verdict, text) in [
        (Verdict::Conditional, "conditional"),
        (Verdict::VerifiesOtherwise, "verifies-otherwise"),
        (Verdict::RefusesOtherwise, "refuses-otherwise"),
        (Verdict::Blocked, "blocked"),
    ] {
        assert_eq!(verdict.to_string(), text);
        assert_eq!(serde_json::to_string(&verdict).unwrap(), format!("\"{text}\""));
        assert_eq!(serde_json::from_str::<Verdict>(&format!("\"{text}\"")).unwrap(), verdict);
    }
    for refused in ["Conditional", "verifies-otherwise ", "otherwise", "blocked:1"] {
        assert!(serde_json::from_str::<Verdict>(&format!("\"{refused}\"")).is_err(), "{refused}");
    }
    assert_eq!(serde_json::to_string(&Pin::Conditional).unwrap(), "\"conditional\"");
    assert_eq!(serde_json::from_str::<Pin>("\"conditional\"").unwrap(), Pin::Conditional);
    assert_eq!(Pin::Conditional.label(), "conditional");
}

// --- the checked-in table, and the scripts it must agree with --------------------

/// A table path as the scripts write it: relative to the checkout.
fn relative(root: &Path, source: &Path) -> String {
    source.strip_prefix(root).expect("a case is in the checkout").display().to_string()
}

/// A corpus script as its commands: the lines that are neither blank nor a
/// comment, without their indentation, a line that ends in `\` joined to the
/// next. A command is compared whole, so one that gains an argument, a
/// variable or a redirection is another command, and an indented row is a row.
struct Script {
    path: &'static str,
    /// The commands that start with the script's row word.
    rows: Vec<String>,
    /// Every other command, in order.
    code: Vec<String>,
}

fn commands(text: &str) -> Vec<String> {
    let mut commands = Vec::new();
    let mut open: Option<String> = None;
    for line in text.lines() {
        let line = line.trim();
        if open.is_none() && (line.is_empty() || line.starts_with('#')) {
            continue;
        }
        let command = match open.take() {
            Some(head) => format!("{head} {line}"),
            None => line.to_owned(),
        };
        match command.strip_suffix('\\') {
            Some(head) => open = Some(head.trim_end().to_owned()),
            None => commands.push(command),
        }
    }
    assert_eq!(open, None, "the script ends inside a command");
    commands
}

impl Script {
    /// `path` in `root`; `row` is the word its rows start with, when its rows
    /// are commands of its own.
    fn read(root: &Path, path: &'static str, row: Option<&str>) -> Self {
        let text = fs::read_to_string(root.join(path)).unwrap();
        let is_row = |command: &String| row.is_some_and(|word| command.starts_with(word));
        let (rows, code) = commands(&text).into_iter().partition(is_row);
        Self { path, rows, code }
    }

    /// The script has `command`, whole.
    #[track_caller]
    fn has(&self, command: &str) {
        assert!(
            self.code.iter().any(|line| line == command),
            "{} no longer has the command `{command}`",
            self.path
        );
    }

    /// The script's commands that hold `word` are exactly `expected`, in order.
    #[track_caller]
    fn holding(&self, word: &str, expected: &[&str]) {
        let found: Vec<&str> =
            self.code.iter().map(String::as_str).filter(|line| line.contains(word)).collect();
        assert_eq!(found, expected, "the commands of {} that hold `{word}`", self.path);
    }

    /// The value of the script's `NAME='…'` command.
    #[track_caller]
    fn literal(&self, variable: &str) -> &str {
        let assignment = format!("{variable}='");
        self.code
            .iter()
            .find_map(|line| line.strip_prefix(&assignment)?.strip_suffix('\''))
            .unwrap_or_else(|| panic!("{} no longer has {variable}='…'", self.path))
    }

    /// The SHA-256 of the commands that are not rows, a newline between two.
    fn digest(&self) -> String {
        use sha2::{Digest as _, Sha256};
        format!("{:x}", Sha256::digest(self.code.join("\n").as_bytes()))
    }

    /// Every command that is not a row is one this test was written against.
    /// The assertions before this one name the commands a verdict turns on and
    /// say which of them moved; this one holds the rest, which no list of
    /// commands can (a variable exported for every compile, a changed branch
    /// of the function that decides a row).
    #[track_caller]
    fn is_the_code_read(&self, sha256: &str) {
        assert_eq!(
            self.digest(),
            sha256,
            "the commands of {} are not the ones tests/corpora.toml was written against. Read \
             what changed in the script against the corpus's rows in the table and against \
             corpus_delta/judge.rs; when they ask the same of every case, record the digest on \
             the left here",
            self.path
        );
    }
}

#[test]
fn a_script_is_read_as_whole_commands() {
    let text = "#!/bin/sh\n# a comment\n\nrun pass \"\" a.rs\n  run fail \"-Z x\" b.rs\n\
                f() { # run <file>\n  \"$TC\" --flag \\\n      \"$1\" \\\n    > log 2>&1\n\
                \x20 # not a command\n}\nNEEDLE='a text'\n";
    assert_eq!(
        commands(text),
        [
            "run pass \"\" a.rs",
            "run fail \"-Z x\" b.rs",
            "f() { # run <file>",
            "\"$TC\" --flag \"$1\" > log 2>&1",
            "}",
            "NEEDLE='a text'",
        ]
    );
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("s.sh"), text).unwrap();
    let script = Script::read(directory.path(), "s.sh", Some("run "));
    assert_eq!(script.rows, ["run pass \"\" a.rs", "run fail \"-Z x\" b.rs"], "indented or not");
    assert_eq!(script.code.len(), 4);
    assert_eq!(script.literal("NEEDLE"), "a text");
    script.has("\"$TC\" --flag \"$1\" > log 2>&1");
    script.holding("\"$TC\"", &["\"$TC\" --flag \"$1\" > log 2>&1"]);
    let digest = "8e7f66b15a6281ea84da71f854aeb5b738e1b7b305dc3f1218ba6a277b0a81f8";
    script.is_the_code_read(digest);
    // A command is held whole: one that gains a variable or an argument is
    // another command, and a new command is another script. A row or a
    // comment is neither.
    let changes = [
        ("  \"$TC\" --flag", "  DEBUG=1 \"$TC\" --flag", true),
        ("    > log 2>&1", "    -Zoff > log 2>&1", true),
        ("NEEDLE='a text'", "NEEDLE='a text'\nexport DEBUG=1", true),
        ("# a comment", "# another comment", false),
        ("run pass \"\" a.rs", "run pass \"\" a.rs\n    run pass \"\" c.rs", false),
    ];
    for (from, to, another) in changes {
        assert!(text.contains(from), "{from:?}");
        fs::write(directory.path().join("s.sh"), text.replacen(from, to, 1)).unwrap();
        let changed = Script::read(directory.path(), "s.sh", Some("run "));
        assert_eq!(changed.digest() != digest, another, "{from:?} -> {to:?}");
        assert_eq!(changed.code != script.code, another, "{from:?} -> {to:?}");
    }
    assert_eq!(Script::read(directory.path(), "s.sh", Some("run ")).rows.len(), 3);
}

#[test]
fn the_checked_in_table_carries_bench_probes_and_ladder() {
    let table = table::load(&checkout()).unwrap();
    let count = |corpus: &Corpus, pin: Pin| {
        corpus.cases.iter().filter(|case| case.pin == Some(pin)).count()
    };
    let bench = corpus(&table, "bench");
    assert_eq!(bench.cases.len(), 71);
    assert_eq!((count(bench, Pin::Verifies), count(bench, Pin::Refuses)), (69, 2));
    let probes = corpus(&table, "probes");
    assert_eq!(probes.cases.len(), 47);
    assert_eq!(
        (
            count(probes, Pin::Verifies),
            count(probes, Pin::Refuses),
            count(probes, Pin::Conditional)
        ),
        (30, 16, 1)
    );
    let ladder = corpus(&table, "ladder");
    assert_eq!(ladder.cases.len(), 73);
    assert_eq!(
        (
            count(ladder, Pin::Verifies),
            count(ladder, Pin::Refuses),
            count(ladder, Pin::Conditional)
        ),
        (38, 29, 6)
    );
    assert_eq!(ladder.dependencies.len(), 9);
    assert_eq!(ladder.cases.iter().filter(|case| case.dependency.is_some()).count(), 20);
    for corpus in [bench, probes, ladder] {
        for case in &corpus.cases {
            assert!(case.pin.is_some(), "{}/{} is pinned", corpus.id, case.id);
            assert_eq!(
                case.certify.is_some(),
                case.pin == Some(Pin::Conditional),
                "{}/{}",
                corpus.id,
                case.id
            );
        }
    }
}

/// The scripts of the first three corpora, held the way the three below are.
/// `corpus_delta::tests::the_table_matches_the_corpus_scripts` has their files
/// and looks for each one's arguments inside its script; here each script's
/// compile is those arguments and nothing else, and no other command of the
/// script has changed.
#[test]
fn the_sweep_battery_and_idiomatic_scripts_compile_what_the_table_says() {
    let root = checkout();
    let table = table::load(&root).unwrap();
    let found =
        "[ -x \"$TC\" ] || { echo \"no trustc at $TC (build it, or pass a path)\"; exit 2; }";
    let version = "echo \"compiler: $(\"$TC\" --version 2>&1 | head -1)\"";
    let logged = "\"$TC\" <args> --out-dir \"$WORK\" \"$f\" > \"$WORK/$n.log\" 2>&1";
    let scripts: [(&str, &'static str, &[&str], &str, &str); 3] = [
        (
            "sweep",
            "scripts/ordinary_rust_sweep.sh",
            &[found, version],
            logged,
            "f7d7b64b1120958adf4ca2f33208f99207c2d2d2f605c8ca48ca7ce1bd5bbde6",
        ),
        (
            "battery",
            "scripts/panicking_std_battery.sh",
            &[found, version],
            logged,
            "fbbd9270245bfc6a75c13eb785932d5809dbf9beaa31ddc8e92038e7c9bc7c8d",
        ),
        (
            "idiomatic",
            "scripts/idiomatic_rust_sample.sh",
            &["[ -x \"$TC\" ] || { echo \"no trustc at $TC\" >&2; exit 2; }"],
            "out=\"$(\"$TC\" <args> --out-dir \"$W/out\" \"$f\" 2>&1)\"",
            "f131baffbed87643a0c0ec9ff330ad4309c3461b44ee20cf50b6902e5a66f831",
        ),
    ];
    for (id, path, before, compile, digest) in scripts {
        let corpus = corpus(&table, id);
        let args = &corpus.cases[0].args;
        for case in &corpus.cases {
            assert_eq!(&case.args, args, "{id}/{}", case.id);
            assert!(case.env.is_empty() && case.dependency.is_none(), "{id}/{}", case.id);
        }
        let script = Script::read(&root, path, None);
        let compile = compile.replace("<args>", &args.join(" "));
        let mut expected = before.to_vec();
        expected.push(&compile);
        script.holding("\"$TC\"", &expected);
        script.is_the_code_read(digest);
    }
}

/// `scripts/daily_driver_bench.sh` holds its 71 programs inline; the table's
/// are files. Each file is the script's source and a newline, the script's one
/// compile is the table's arguments and nothing else, and the two cases pinned
/// `refuses` are the script's correct refusals.
#[test]
fn the_bench_table_matches_its_script() {
    let root = checkout();
    let table = table::load(&root).unwrap();
    let bench = corpus(&table, "bench");
    let script = Script::read(&root, "scripts/daily_driver_bench.sh", Some("b "));
    let mut rows = BTreeSet::new();
    for line in &script.rows {
        let mut words = line[2..].trim_start().splitn(2, char::is_whitespace);
        let category = words.next().unwrap();
        let mut words = words.next().unwrap().trim_start().splitn(2, char::is_whitespace);
        let name = words.next().unwrap();
        let source = words
            .next()
            .and_then(|rest| rest.trim_start().strip_prefix('\''))
            .and_then(|rest| rest.strip_suffix('\''))
            .unwrap_or_else(|| panic!("not a `b <category> <name> '<source>'` row: {line}"));
        assert!(!source.contains('\''), "{line}");
        let id = format!("{category}/{name}");
        let file = root.join(format!("tests/daily-driver-bench/{category}/{name}.rs"));
        // The script compiles `$WORK/<name>.rs`, so the crate is `<name>`.
        assert_eq!(case(bench, &id).source, file, "{id}");
        assert_eq!(fs::read_to_string(&file).unwrap(), format!("{source}\n"), "{id}");
        assert!(rows.insert(id), "the script has {category}/{name} twice");
    }
    let cases: BTreeSet<String> = bench.cases.iter().map(|case| case.id.clone()).collect();
    assert_eq!(cases, rows, "one case for each row of the script, and no other");
    // The script's one compile, whole: every case's arguments, no variable,
    // and nothing after the source.
    script.has("tot=$((tot+1)); printf '%s\\n' \"$3\" > \"$WORK/$2.rs\"");
    let args = &bench.cases[0].args;
    let compile =
        format!("out=$(\"$TC\" {} --out-dir \"$WORK/out\" \"$WORK/$2.rs\" 2>&1)", args.join(" "));
    script.holding(
        "\"$TC\"",
        &[
            "[ -x \"$TC\" ] || { echo \"no trustc at $TC (build it, or pass a path)\"; exit 2; }",
            "echo \"compiler: $(\"$TC\" --version 2>&1 | head -1)\"",
            compile.as_str(),
        ],
    );
    for case in &bench.cases {
        assert_eq!(&case.args, args, "{}", case.id);
        assert!(case.env.is_empty() && case.log_contains.is_none() && case.dependency.is_none());
    }
    // The script's exit is "every case verifies"; the two it names as correct
    // refusals are the two pinned `refuses`.
    script.has(
        "if [ $? -eq 0 ]; then pass=$((pass+1)); printf '  PASS  %-8s %s\\n' \"$1\" \"$2\"; \
         return; fi",
    );
    script.has("[ \"$pass\" -eq \"$tot\" ]");
    let assignment = script
        .code
        .iter()
        .find_map(|line| line.strip_prefix("CORRECT_REFUSAL=\"")?.strip_suffix('"'))
        .expect("the script names its correct refusals");
    let correct: BTreeSet<&str> = assignment.split_whitespace().collect();
    let refuses: BTreeSet<&str> = bench
        .cases
        .iter()
        .filter(|case| case.pin == Some(Pin::Refuses))
        .map(|case| case.id.as_str())
        .collect();
    assert_eq!(refuses, correct);
    assert!(bench.cases.iter().all(|case| case.pin.is_some()));
    script.is_the_code_read("64c5e476ecdde9e260852bd501060530a66458d9fea90ff3dfc399347a6f582a");
    // The files are held to the script's bytes, which are not the formatter's:
    // the tree is in rustfmt.toml's `ignore`, or `x.py fmt` rewrites all 71.
    let ignored = fs::read_to_string(root.join("rustfmt.toml")).unwrap();
    assert!(
        ignored.lines().any(|line| line.trim() == "\"/tests/daily-driver-bench/\","),
        "rustfmt.toml no longer ignores /tests/daily-driver-bench/"
    );
}

/// `scripts/daily_driver_probes.sh` has one `run <expect> <edition> <flags>
/// <file>` line for each probe; the table has the same file, arguments and pin
/// for each, and the script's two texts for `conditional`.
#[test]
fn the_probes_table_matches_its_script() {
    let root = checkout();
    let table = table::load(&root).unwrap();
    let probes = corpus(&table, "probes");
    let script = Script::read(&root, "scripts/daily_driver_probes.sh", Some("run "));
    script.has("D=tests/daily-driver-realistic");
    script.has("L=$D/lean");
    let certify = Certify {
        args: strings(&["-Ztrust-policy=certify"]),
        refusal: script.literal("CERT_NEEDLE").to_owned(),
    };
    let disclosure = script.literal("COND_NEEDLE");
    let mut rows = BTreeSet::new();
    fn malformed(line: &str) -> ! {
        panic!("not a `run <expect> <edition> \"<flags>\" <file>` row: {line}")
    }
    for line in &script.rows {
        let mut quoted = line.splitn(3, '"');
        let (head, flags, file) = (quoted.next(), quoted.next(), quoted.next());
        let (Some(head), Some(flags), Some(file)) = (head, flags, file) else { malformed(line) };
        let head: Vec<&str> = head.split_whitespace().collect();
        let [_, expect, edition] = head[..] else { malformed(line) };
        let file = file.trim();
        let file = match (file.strip_prefix("$D/"), file.strip_prefix("$L/")) {
            (Some(file), _) => format!("tests/daily-driver-realistic/{file}"),
            (_, Some(file)) => format!("tests/daily-driver-realistic/lean/{file}"),
            _ => malformed(line),
        };
        let id = Path::new(&file).file_stem().unwrap().to_str().unwrap().to_owned();
        let case = case(probes, &id);
        assert_eq!(relative(&root, &case.source), file, "{id}");
        let mut args: Vec<&str> = flags.split_whitespace().collect();
        args.extend(["--crate-type=lib", "--edition", edition]);
        assert_eq!(case.args, args, "{id}");
        let pin = match expect {
            "pass" => Pin::Verifies,
            "fail" => Pin::Refuses,
            "conditional" => Pin::Conditional,
            _ => malformed(line),
        };
        assert_eq!(case.pin, Some(pin), "{id}");
        if pin == Pin::Conditional {
            assert_eq!(case.log_contains.as_deref(), Some(disclosure), "{id}");
            assert_eq!(case.certify.as_ref(), Some(&certify), "{id}");
        } else {
            assert_eq!((&case.log_contains, &case.certify), (&None, &None), "{id}");
        }
        assert!(case.env.is_empty() && case.dependency.is_none(), "{id}");
        assert!(rows.insert(id.clone()), "the script has {id} twice");
    }
    let cases: BTreeSet<String> = probes.cases.iter().map(|case| case.id.clone()).collect();
    assert_eq!(cases, rows, "one case for each row of the script, and no other");
    // The script's two compiles, whole. The certify compile is the first with
    // one more argument; the verb appends it where the script puts it after
    // the row's flags (the table's header lists that).
    script.has("local expect=$1 ed=$2 flags=$3 file=$4 name");
    script.holding(
        "\"$TC\"",
        &[
            "[ -x \"$TC\" ] || { echo \"no trustc at $TC (build it, or pass a path)\"; exit 2; }",
            "echo \"compiler: $(\"$TC\" --version 2>&1 | head -1)\"",
            "\"$TC\" $flags --crate-type=lib --edition \"$ed\" --out-dir \"$WORK\" \"$ROOT/$file\" \
             >\"$WORK/$name.log\" 2>&1",
            "\"$TC\" $flags -Ztrust-policy=certify --crate-type=lib --edition \"$ed\" --out-dir \
             \"$WORK\" \"$ROOT/$file\" >\"$WORK/$name.certify.log\" 2>&1",
        ],
    );
    // What `conditional` asks of them.
    script.has("local got=pass; [ $rc -eq 0 ] || got=fail");
    script.has("if [ \"$expect\" = conditional ] && [ \"$got\" = pass ]; then");
    script.has("if ! grep -qF -- \"$COND_NEEDLE\" \"$WORK/$name.log\"; then");
    script
        .has("if [ $crc -ne 0 ] && grep -qF -- \"$CERT_NEEDLE\" \"$WORK/$name.certify.log\"; then");
    script.is_the_code_read("de28f093c1b6fcdc0f172db403f1ac3160d3e3a4862d94b24073c9f9c37784c0");
}

/// The first `//@ <name>:` line's value, as `scripts/open_dispatch_ladder.sh`
/// reads it (`sed -n 's|^//@ <name>: *||p' | head -1`): written here a second
/// time, apart from `headers.rs`, so the two are compared.
fn sed_header(text: &str, name: &str) -> String {
    let prefix = format!("//@ {name}:");
    text.split('\n')
        .find(|line| line.starts_with(&prefix))
        .map(|line| line[prefix.len()..].trim_start_matches(' ').to_owned())
        .unwrap_or_default()
}

/// `scripts/open_dispatch_ladder.sh` reads each row from its file, so the
/// table and the script share the rows; what can part is how each reads them
/// and what each compiles. This holds the script's own lines, and each case
/// against a second reading of its file.
#[test]
fn the_ladder_table_matches_its_script() {
    let root = checkout();
    let table = table::load(&root).unwrap();
    let ladder = corpus(&table, "ladder");
    let script = Script::read(&root, "scripts/open_dispatch_ladder.sh", None);
    let directory = "tests/open-dispatch-ladder";
    script.has("DIR=\"$ROOT/tests/open-dispatch-ladder\"");
    // Its loops: the rows, the dependencies, the rows built against them.
    script.holding(
        "for ",
        &[
            "for f in \"$DIR\"/*.rs; do",
            "for dep in \"$DIR\"/xcrate/lib*.rs; do",
            "for f in \"$DIR\"/xcrate/user_*.rs; do",
        ],
    );
    // The headers each loop reads, and how.
    script.holding(
        "sed -n 's|^//@ ",
        &[
            "exp=\"$(sed -n 's|^//@ trust-ladder: *||p' \"$f\" | head -1)\"",
            "needle=\"$(sed -n 's|^//@ trust-ladder-row: *||p' \"$f\" | head -1)\"",
            "ct=\"$(sed -n 's|^//@ trust-ladder-crate-type: *||p' \"$f\" | head -1)\"",
            "depflags=($(sed -n 's|^//@ trust-ladder-dep-flags: *||p' \"$dep\" | head -1))",
            "exp=\"$(sed -n 's|^//@ trust-ladder-xcrate: *||p' \"$f\" | head -1)\"",
            "dn=\"$(sed -n 's|^//@ trust-ladder-xcrate-dep: *||p' \"$f\" | head -1)\"; \
             dn=\"${dn:-libt}\"",
            "decl=\"$(sed -n 's|^//@ trust-ladder-xcrate-declare: *||p' \"$f\" | head -1)\"",
            "xct=\"$(sed -n 's|^//@ trust-ladder-crate-type: *||p' \"$f\" | head -1)\"",
            "needle=\"$(sed -n 's|^//@ trust-ladder-row: *||p' \"$f\" | head -1)\"",
        ],
    );
    // What each kind of row is compiled with, whole: only a row of the first
    // loop is given the variable, a certify compile is its compile with one
    // more argument and no variable, and a dependency is given none.
    script.has("if [ \"$ct\" = bin ]; then ctflag=(); else ctflag=(--crate-type=lib); fi");
    script.has("if [ \"$xct\" = lib ]; then xctflag=(--crate-type=lib); else xctflag=(); fi");
    script.has(
        "if [ -n \"$decl\" ]; then declflag=(\"-Ztrust-bundle-foreign-crate=$decl\"); else \
         declflag=(); fi",
    );
    script.has(
        "[ -f \"$L/lib$dn.rlib\" ] || { echo \"DIVERGED xcrate/$n: dependency $dn absent\"; \
         diverged=$((diverged+1)); continue; }",
    );
    script.holding(
        "\"$TC\"",
        &[
            "[ -x \"$TC\" ] || { echo \"no trustc at $TC\" >&2; exit 2; }",
            "TRUST_VANILLA_DEBUG=1 \"$TC\" --edition 2021 ${ctflag[@]+\"${ctflag[@]}\"} --out-dir \
             \"$o\" \"$f\" > \"$WORK/$n.log\" 2>&1",
            "\"$TC\" --edition 2021 ${ctflag[@]+\"${ctflag[@]}\"} -Ztrust-policy=certify --out-dir \
             \"$o.certify\" \"$f\" > \"$WORK/$n.certify.log\" 2>&1",
            "if ! \"$TC\" --edition 2021 --crate-type=lib -Zalways-encode-mir \
             ${depflags[@]+\"${depflags[@]}\"} --out-dir \"$L\" \"$dep\" > \"$WORK/$dn.log\" 2>&1; \
             then",
            "\"$TC\" --edition 2021 ${xctflag[@]+\"${xctflag[@]}\"} --extern \
             \"$dn=$L/lib$dn.rlib\" -L \"$L\" ${declflag[@]+\"${declflag[@]}\"} --out-dir \"$o\" \
             \"$f\" > \"$WORK/$n.log\" 2>&1",
            "\"$TC\" --edition 2021 ${xctflag[@]+\"${xctflag[@]}\"} --extern \
             \"$dn=$L/lib$dn.rlib\" -L \"$L\" ${declflag[@]+\"${declflag[@]}\"} \
             -Ztrust-policy=certify --out-dir \"$o.certify\" \"$f\" > \"$WORK/$n.certify.log\" \
             2>&1",
        ],
    );
    // What decides a row.
    script.has("[ -n \"$exp\" ] || continue");
    script.has("local got; if [ \"$rc\" -eq 0 ]; then got=verifies; else got=refuses; fi");
    script.has("if [ \"$exp\" = conditional ]; then");
    script.has("if [ \"$got\" != verifies ]; then");
    script.has("[ -n \"$needle\" ] || needle=\"$COND_NEEDLE\"");
    script.has(
        "if [ -z \"$crc\" ] || [ \"$crc\" -eq 0 ] || ! grep -qF -- \"$CERT_NEEDLE\" \"$clog\"; \
         then",
    );
    script.has("if [ \"$got\" != \"$exp\" ]; then");
    script.has("if [ -n \"$needle\" ] && ! grep -qF -- \"$needle\" \"$log\"; then");
    script.is_the_code_read("d38b2230cf5c42e378dac800500aa183ca80fb71b1608e08ebc0b32c01c70cd1");
    let disclosure = script.literal("COND_NEEDLE");
    let certify = Certify {
        args: strings(&["-Ztrust-policy=certify"]),
        refusal: script.literal("CERT_NEEDLE").to_owned(),
    };

    // Every file the script's two loops read is a case, read the same way.
    let files = |sub: &str, prefix: &str| -> Vec<(String, String)> {
        let mut found: Vec<(String, String)> = fs::read_dir(root.join(directory).join(sub))
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|extension| extension == "rs"))
            .map(|path| {
                let stem = path.file_stem().unwrap().to_str().unwrap().to_owned();
                (stem, fs::read_to_string(&path).unwrap())
            })
            .filter(|(stem, _)| stem.starts_with(prefix))
            .collect();
        found.sort();
        found
    };
    let pin_of = |word: &str, id: &str| match word {
        "verifies" => Pin::Verifies,
        "refuses" => Pin::Refuses,
        "conditional" => Pin::Conditional,
        other => panic!("{id}: its header says {other:?}"),
    };
    let needle_of = |file: &str, pin: Pin| match sed_header(file, "trust-ladder-row") {
        needle if needle.is_empty() && pin == Pin::Conditional => Some(disclosure.to_owned()),
        needle if needle.is_empty() => None,
        needle => Some(needle),
    };
    let mut rows = BTreeSet::new();
    for (stem, file) in files("", "") {
        let case = case(ladder, &stem);
        let pin = pin_of(&sed_header(&file, "trust-ladder"), &stem);
        assert_eq!(case.pin, Some(pin), "{stem}");
        let mut args = vec!["--edition", "2021"];
        if sed_header(&file, "trust-ladder-crate-type") != "bin" {
            args.push("--crate-type=lib");
        }
        assert_eq!(case.args, args, "{stem}");
        assert_eq!(case.env, [("TRUST_VANILLA_DEBUG".to_owned(), "1".to_owned())], "{stem}");
        assert_eq!(case.log_contains, needle_of(&file, pin), "{stem}");
        assert_eq!(case.certify.as_ref(), (pin == Pin::Conditional).then_some(&certify), "{stem}");
        assert_eq!(case.dependency, None, "{stem}");
        rows.insert(stem);
    }
    for (stem, file) in files("xcrate", "user_") {
        let id = format!("xcrate/{stem}");
        let case = case(ladder, &id);
        let pin = pin_of(&sed_header(&file, "trust-ladder-xcrate"), &id);
        assert_eq!(case.pin, Some(pin), "{id}");
        let mut args = vec!["--edition", "2021"];
        if sed_header(&file, "trust-ladder-crate-type") == "lib" {
            args.push("--crate-type=lib");
        }
        assert_eq!(case.args, args, "{id}");
        assert!(case.env.is_empty(), "{id}");
        assert_eq!(case.log_contains, needle_of(&file, pin), "{id}");
        assert_eq!(case.certify.as_ref(), (pin == Pin::Conditional).then_some(&certify), "{id}");
        let name = match sed_header(&file, "trust-ladder-xcrate-dep") {
            name if name.is_empty() => "libt".to_owned(),
            name => name,
        };
        let then_args = match sed_header(&file, "trust-ladder-xcrate-declare") {
            declared if declared.is_empty() => Vec::new(),
            declared => vec![format!("-Ztrust-bundle-foreign-crate={declared}")],
        };
        assert_eq!(case.dependency, Some(DependencyUse { name, then_args }), "{id}");
        rows.insert(id);
    }
    let cases: BTreeSet<String> = ladder.cases.iter().map(|case| case.id.clone()).collect();
    assert_eq!(cases, rows, "one case for each file the script reads a row from, and no other");

    let dependencies = files("xcrate", "lib");
    assert_eq!(ladder.dependencies.len(), dependencies.len());
    for (stem, file) in dependencies {
        let dependency = ladder
            .dependencies
            .iter()
            .find(|dependency| dependency.name == stem)
            .unwrap_or_else(|| panic!("{stem} is no dependency of the table"));
        assert_eq!(dependency.id, format!("xcrate/{stem}"));
        assert_eq!(relative(&root, &dependency.source), format!("{directory}/xcrate/{stem}.rs"));
        let mut args = strings(&["--edition", "2021", "--crate-type=lib", "-Zalways-encode-mir"]);
        args.extend(
            sed_header(&file, "trust-ladder-dep-flags").split_whitespace().map(str::to_owned),
        );
        assert_eq!(dependency.args, args, "{stem}");
    }
}
