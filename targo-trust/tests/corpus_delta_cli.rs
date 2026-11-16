//! `targo trust gate corpus-delta`, the built executable against fake
//! compilers on disk: what the unit tests' stand-in runner cannot show. The
//! compilers are shell scripts this test writes; each answers `-vV` and then
//! verifies, refuses, crashes, hangs or disappears per file.
//!
//! The bracketed numbers are the checks of the shell test this replaces
//! (`scripts/tests/seal_corpus_delta_test.sh`, deleted with the script). The
//! rank, the pins and the report's wording are held by the unit tests
//! (`corpus_delta::tests`), through the same `run_with` this executable calls.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(unix)]

use std::fs;
use std::os::unix::fs::PermissionsExt as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const TABLE: &str = r#"schema = "trust.corpora.v1"

[[corpus]]
id = "sweep"
glob = "corpora/sweep/*.rs"
args = ["--crate-type=lib", "--edition", "2021"]

[[corpus]]
id = "lean"
args = ["--crate-type=lib"]

[[corpus.case]]
id = "island"
file = "corpora/lean/island.rs"
args = ["-Z", "trust-verify=off", "--crate-type=lib", "--edition", "2024"]
pin = "verifies"
"#;

/// The sweep file the `*-one` compilers single out.
const VICTIM: &str = "a.rs";
const SWEEP: [&str; 3] = ["a", "b", "c"];

/// The variables no compiler under comparison may inherit.
const HOST_JOBSERVER: [&str; 2] = ["TRUST_MEMORY_JOBSERVER_SOCK", "TRUST_MEMORY_JOBSERVER"];

/// A checkout with a table, two corpora, and a directory of fake compilers.
struct World {
    root: tempfile::TempDir,
}

impl World {
    fn new() -> Self {
        let world = Self { root: tempfile::tempdir().unwrap() };
        world.write("tests/corpora.toml", TABLE);
        for case in SWEEP {
            world.write(&format!("corpora/sweep/{case}.rs"), "pub fn f() {}\n");
        }
        world.write(
            "corpora/lean/island.rs",
            "clean {\n  theorem t : True := trivial\n}\n\npub fn f() {}\n",
        );
        fs::create_dir_all(world.path("bin")).unwrap();
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

    /// Write the fake compiler `bin/<name>`: it answers `-vV` with `commit`,
    /// then runs `body` (shell; `$victim` is 1 when the victim file is among
    /// its arguments), then verifies.
    fn compiler(&self, name: &str, commit: char, body: &str) -> PathBuf {
        let commit = commit.to_string().repeat(40);
        let script = format!(
            "#!/bin/sh\n\
             case \"${{1:-}}\" in\n\
             \x20 -vV) printf 'rustc 0.0.0-fake\\nbinary: trustc\\ncommit-hash: %s\\ncommit-date: \
             2026-01-01\\n' '{commit}'; exit 0 ;;\n\
             esac\n\
             victim=0\n\
             for a in \"$@\"; do\n\
             \x20 [ \"$(basename -- \"$a\")\" = '{VICTIM}' ] && victim=1\n\
             done\n\
             {body}\n\
             exit 0\n"
        );
        let path = self.path(&format!("bin/{name}"));
        fs::write(&path, script).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
        path
    }

    fn accept(&self) -> PathBuf {
        self.compiler("accept", '1', "")
    }

    fn refuse_one(&self) -> PathBuf {
        self.compiler(
            "refuse-one",
            '2',
            "[ \"$victim\" = 1 ] && { echo \"error: fake refuse-one of a.rs\" >&2; exit 1; }",
        )
    }

    /// The verb, in `cwd`, with none of the host's jobserver variables unless
    /// the test sets them.
    fn verb(&self, cwd: &Path) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_targo-trust"));
        command.args(["trust", "gate", "corpus-delta"]).current_dir(cwd);
        for name in HOST_JOBSERVER {
            command.env_remove(name);
        }
        command
    }

    /// The delta from `old` to `new` over this checkout, named by `--repo-root`.
    fn delta(&self, old: &Path, new: &Path, rest: &[&str]) -> Run {
        let mut command = self.verb(self.root.path());
        command.arg("--old").arg(old).arg("--new").arg(new);
        command.arg("--repo-root").arg(self.root.path()).args(rest);
        Run::of(command.output().unwrap())
    }

    /// One side's kept record: (corpus, case, verdict) per line.
    fn kept(&self, keep: &str, side: &str) -> Vec<(String, String, String)> {
        fs::read_to_string(self.path(keep).join(side).join("record.ndjson"))
            .unwrap()
            .lines()
            .map(|line| {
                let record: serde_json::Value = serde_json::from_str(line).unwrap();
                let field = |name: &str| record[name].as_str().unwrap().to_owned();
                (field("corpus"), field("case"), field("verdict"))
            })
            .collect()
    }
}

struct Run {
    code: i32,
    stdout: String,
    stderr: String,
}

impl Run {
    fn of(output: Output) -> Self {
        Self {
            code: output.status.code().expect("the verb exits; it is not signalled"),
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        }
    }

    fn all(&self) -> String {
        format!("exit {}\n--- stdout\n{}--- stderr\n{}", self.code, self.stdout, self.stderr)
    }

    /// The flip lines on either stream, as the shell test counted them.
    fn flips(&self) -> Vec<&str> {
        self.stdout
            .lines()
            .chain(self.stderr.lines())
            .filter(|line| {
                ["LOSS ", "GAIN ", "GONE ", "NEW "].iter().any(|kind| line.starts_with(kind))
            })
            .collect()
    }
}

const LOSS: &str = "LOSS  sweep/a: verifies -> refuses: error: fake refuse-one of a.rs";

/// [1-5], with real processes: the report is on stdout, and it exits 0.
#[test]
fn two_real_compilers_are_compared_case_by_case() {
    let world = World::new();
    let (accept, refuse_one) = (world.accept(), world.refuse_one());
    let run = world.delta(&accept, &refuse_one, &["--corpora", "sweep"]);
    assert_eq!(run.code, 0, "{}", run.all());
    assert_eq!(run.flips(), [LOSS], "{}", run.all());
    // The fixture checkout is no Git repository, so it has no HEAD to compare
    // a compiler's commit with.
    let expected = format!(
        "old: rustc 0.0.0-fake | {} 2026-01-01\n     {}\n\
         new: rustc 0.0.0-fake | {} 2026-01-01\n     {}\n\
         corpora: sweep (this checkout, unknown)\n\
         not compared: lean (not named by --corpora)\n\n{LOSS}\n\ncorpus ",
        "1".repeat(40),
        accept.display(),
        "2".repeat(40),
        refuse_one.display()
    );
    assert!(run.stdout.starts_with(&expected), "{}", run.all());
    assert!(run.stdout.ends_with("\nseal corpus delta: 1 lost, 0 gained\n"), "{}", run.all());
    assert!(run.stderr.contains("corpus-delta: old: sweep (3 case(s))"), "{}", run.all());

    let failing = world.delta(&accept, &refuse_one, &["--corpora", "sweep", "--fail-on-loss"]);
    assert_eq!(failing.code, 1, "{}", failing.all());
    assert_eq!(failing.stdout, run.stdout, "exit 1 prints the same report on stdout");
    let same = world.delta(&accept, &accept, &["--fail-on-loss"]);
    assert_eq!(same.code, 0, "{}", same.all());
    assert!(same.flips().is_empty(), "identical compilers print no flip:\n{}", same.all());
}

/// [15] [16]
#[test]
fn a_missing_compiler_and_a_directory_exit_2() {
    let world = World::new();
    let accept = world.accept();
    fs::create_dir_all(world.path("bin/a-directory")).unwrap();
    for absent in ["absent", "a-directory"] {
        let run = world.delta(&accept, &world.path(&format!("bin/{absent}")), &[]);
        assert_eq!(run.code, 2, "{absent}:\n{}", run.all());
        assert!(run.stderr.contains("no executable compiler at"), "{}", run.all());
        assert!(run.stdout.is_empty(), "{}", run.all());
    }
}

/// [17]
#[test]
fn a_compiler_whose_version_query_fails_exits_3_before_any_case_runs() {
    let world = World::new();
    let accept = world.accept();
    let broken = world.path("bin/broken");
    fs::write(&broken, "#!/bin/sh\necho 'cannot load the driver' >&2\nexit 1\n").unwrap();
    fs::set_permissions(&broken, fs::Permissions::from_mode(0o755)).unwrap();
    let keep = world.path("kept");
    let run =
        world.delta(&accept, &broken, &["--corpora", "sweep", "--keep", keep.to_str().unwrap()]);
    assert_eq!(run.code, 3, "{}", run.all());
    assert!(run.stderr.contains("COULD NOT RUN"), "{}", run.all());
    assert!(run.stderr.contains("does not run: `-vV` exited 1"), "{}", run.all());
    assert!(run.stderr.contains("cannot load the driver"), "{}", run.all());
    assert!(run.flips().is_empty(), "{}", run.all());
    assert!(!keep.join("old/record.ndjson").exists(), "no case may run before both answer");
}

/// [18]
#[test]
fn an_unknown_corpus_exits_2() {
    let world = World::new();
    let accept = world.accept();
    let run = world.delta(&accept, &accept, &["--corpora", "nonsense"]);
    assert_eq!(run.code, 2, "{}", run.all());
    assert!(run.stderr.contains("unknown corpus: \"nonsense\""), "{}", run.all());
}

/// [19], and the table found from the caller's directory.
#[test]
fn relative_compiler_paths_resolve_against_the_callers_directory() {
    let world = World::new();
    world.accept();
    world.refuse_one();
    // From bin/, two levels of nothing between it and the table.
    let mut command = world.verb(&world.path("bin"));
    command.args(["--old", "accept", "--new", "./refuse-one", "--corpora", "sweep"]);
    let run = Run::of(command.output().unwrap());
    assert_eq!(run.code, 0, "{}", run.all());
    assert_eq!(run.flips(), [LOSS], "{}", run.all());

    // Outside any checkout there is no table to find.
    let elsewhere = tempfile::tempdir().unwrap();
    let mut command = world.verb(elsewhere.path());
    command.arg("--old").arg(world.path("bin/accept")).arg("--new").arg(world.path("bin/accept"));
    let lost = Run::of(command.output().unwrap());
    assert_eq!(lost.code, 2, "{}", lost.all());
    assert!(lost.stderr.contains("no tests/corpora.toml in"), "{}", lost.all());
}

/// [23], for both variables (critique 2).
#[test]
fn the_hosts_jobserver_variables_reach_neither_side() {
    let world = World::new();
    let sensitive = world.compiler(
        "sock-sensitive",
        '5',
        "[ -z \"${TRUST_MEMORY_JOBSERVER_SOCK:-}${TRUST_MEMORY_JOBSERVER:-}\" ] || { echo \
         \"error: saw the host's jobserver\" >&2; exit 1; }",
    );
    for exported in HOST_JOBSERVER {
        // The control: handed the variable directly, this compiler refuses.
        let direct = Command::new(&sensitive)
            .arg(world.path("corpora/sweep/a.rs"))
            .env_remove(HOST_JOBSERVER[0])
            .env_remove(HOST_JOBSERVER[1])
            .env(exported, "/nonexistent/host.sock")
            .output()
            .unwrap();
        assert_eq!(direct.status.code(), Some(1), "{exported}: the fake must see it");

        let keep = format!("kept-{exported}");
        let mut command = world.verb(world.root.path());
        command.env(exported, "/nonexistent/host.sock");
        command.arg("--old").arg(&sensitive).arg("--new").arg(&sensitive);
        command.args(["--corpora", "sweep", "--keep", &keep]);
        let run = Run::of(command.output().unwrap());
        assert_eq!(run.code, 0, "{exported}:\n{}", run.all());
        for side in ["old", "new"] {
            let record = world.kept(&keep, side);
            assert_eq!(record.len(), SWEEP.len(), "{exported} {side}");
            for (corpus, case, verdict) in record {
                assert_eq!(verdict, "verifies", "{exported} reached the {side} {corpus}/{case}");
            }
        }
    }
}

/// [25], as far as it has a native counterpart: a case whose compiler cannot
/// be started could not run, and the case is named.
#[test]
fn a_compiler_that_cannot_be_started_exits_3_and_names_the_case() {
    let world = World::new();
    let accept = world.accept();
    // Answers `-vV`, verifies its first case, and takes itself away.
    let vanishing = world.compiler("vanishing", '6', "rm -f -- \"$0\"");
    let run = world.delta(&accept, &vanishing, &["--corpora", "sweep", "--fail-on-loss"]);
    assert_eq!(run.code, 3, "{}", run.all());
    assert!(
        run.stderr.contains("CORPUS-DELTA: COULD NOT RUN — new: sweep/b: cannot start "),
        "{}",
        run.all()
    );
    assert!(run.flips().is_empty(), "{}", run.all());
}

/// Critique 1: a compiler ended by a signal is `crash:128+signal`.
#[test]
fn a_compiler_ended_by_a_signal_is_a_crash_of_128_plus_the_signal() {
    let world = World::new();
    let refuse_one = world.refuse_one();
    let killed = world.compiler(
        "killed-one",
        '7',
        "[ \"$victim\" = 1 ] && { echo \"error: about to be killed\" >&2; kill -KILL $$; }",
    );
    let run = world.delta(&refuse_one, &killed, &["--corpora", "sweep", "--fail-on-loss"]);
    assert_eq!(run.code, 1, "{}", run.all());
    assert_eq!(
        run.flips(),
        ["LOSS  sweep/a: refuses -> crash:137: error: about to be killed"],
        "{}",
        run.all()
    );
    assert!(run.stdout.contains("the new compiler crashed on 1 case(s)"), "{}", run.all());
}

/// The bound `a_case_past_its_bound_is_not_judged_and_the_run_exits_3` gives
/// every compile, in seconds. One bound covers the five compiles that must
/// finish as well as the one that hangs, so it is far above what a fake
/// compiler (a shell and a few `basename` forks) takes on a loaded host, and
/// the test costs this long once.
const HANG_BOUND_SECONDS: &str = "10";

/// Critique 1: a case past `--case-seconds` is NOT JUDGED, never ranked, and
/// the run exits 3; the compiler is stopped, not left running.
#[test]
fn a_case_past_its_bound_is_not_judged_and_the_run_exits_3() {
    let world = World::new();
    let accept = world.accept();
    let pid_file = world.path("hanging.pid");
    let hanging = world.compiler(
        "hang-one",
        '8',
        &format!(
            "[ \"$victim\" = 1 ] && {{ echo $$ > '{}'; exec sleep 300; }}",
            pid_file.display()
        ),
    );
    let run = world.delta(
        &accept,
        &hanging,
        &[
            "--corpora",
            "sweep",
            "--fail-on-loss",
            "--case-seconds",
            HANG_BOUND_SECONDS,
            "--keep",
            "kept",
        ],
    );
    assert_eq!(run.code, 3, "{}", run.all());
    assert!(
        run.stderr.contains(&format!(
            "NOT JUDGED  new sweep/a: no verdict within {HANG_BOUND_SECONDS}s (log: "
        )),
        "{}",
        run.all()
    );
    assert_eq!(
        run.stderr.lines().filter(|line| line.starts_with("NOT JUDGED ")).count(),
        1,
        "only the hanging compile is past its bound:\n{}",
        run.all()
    );
    assert!(run.stderr.contains("so nothing was compared"), "{}", run.all());
    assert!(run.flips().is_empty(), "a case with no verdict is never ranked:\n{}", run.all());
    assert!(run.stdout.is_empty(), "{}", run.all());
    let new = world.kept("kept", "new");
    assert_eq!(new[0], ("sweep".into(), "a".into(), "not-judged".into()));
    assert_eq!(new[1].2, "verifies", "the side goes on after one case past its bound");
    // The compiler was stopped and reaped, not left behind: nothing has its pid.
    let pid = fs::read_to_string(&pid_file).unwrap_or_else(|error| {
        panic!("the hanging compiler wrote no pid: {error}\n{}", run.all())
    });
    let alive = Command::new("kill").args(["-0", pid.trim()]).output().unwrap();
    assert!(!alive.status.success(), "the compiler (pid {}) outlived its bound", pid.trim());
}

/// R2: a `.rs` file with a `clean { }` island gets its own arguments, on the
/// compiler's real command line, with `--out-dir` and the file after them.
#[test]
fn a_case_with_a_lean_island_gets_its_own_arguments() {
    let world = World::new();
    let accept = world.accept();
    let picky = world.compiler(
        "picky",
        '9',
        "printf '%s\\n' \"$*\"\n\
         case \"$*\" in\n\
         \x20 '-Z trust-verify=off --crate-type=lib --edition 2024 --out-dir '*/island.rs) ;;\n\
         \x20 *) echo \"error: not the island's command line\" >&2; exit 1 ;;\n\
         esac\n\
         grep -q '^clean {' \"$8\" || { echo \"error: no island in $8\" >&2; exit 1; }",
    );
    let run =
        world.delta(&accept, &picky, &["--corpora", "lean", "--fail-on-loss", "--keep", "kept"]);
    assert_eq!(run.code, 0, "{}", run.all());
    assert!(run.flips().is_empty(), "{}", run.all());
    let log = fs::read_to_string(world.path("kept/new/lean/island.log")).unwrap();
    assert!(
        log.starts_with("-Z trust-verify=off --crate-type=lib --edition 2024 --out-dir "),
        "{log}"
    );
    // The control: the same compiler refuses the sweep's command line.
    let sweep = world.delta(&accept, &picky, &["--corpora", "sweep"]);
    assert_eq!(sweep.flips().len(), SWEEP.len(), "{}", sweep.all());
}

#[test]
fn help_is_printed_on_stdout_and_the_gate_table_is_not_asked() {
    let world = World::new();
    let mut command = world.verb(world.root.path());
    let run = Run::of(command.arg("--help").output().unwrap());
    assert_eq!(run.code, 0, "{}", run.all());
    assert!(
        run.stdout.starts_with("Usage: targo trust gate corpus-delta --old TRUSTC"),
        "{}",
        run.all()
    );
    assert!(run.stdout.contains("tests/corpora.toml"), "{}", run.all());
    let mut bare = world.verb(world.root.path());
    let run = Run::of(bare.output().unwrap());
    assert_eq!(run.code, 2, "{}", run.all());
    assert!(run.stderr.contains("--old is required"), "{}", run.all());
}
