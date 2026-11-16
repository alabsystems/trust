//! `targo trust land --check`, the built executable over a Git repository this
//! test makes: what the unit tests' `run_with` cannot show. The exit status
//! the process returns, the stream its report is on, the `main.rs` arm that
//! reaches the verb, and a row's command as a real child of the real verb.
//!
//! The table's rules fix a row's command (`python3 -B scripts/land_gate.py
//! validation-tests <module>`), so the test puts a `python3` of its own first
//! on the verb's `PATH`: a shell script that records its directory and its
//! arguments and then ends as the test said that module ends. Selection, the
//! table's refusals and the report's wording are held by the unit tests
//! (`land::tests`), through the same `run_with` this executable calls.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(unix)]

use std::fs;
use std::os::unix::fs::PermissionsExt as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const FOOTER: &str = "validation rows only; this is not the landing gate";
const COUNTS: &str = "2 of 2 rows are not yet a targo verb or test target\n\
     not run: 2 [[not_run]] row(s): 1 red, 1 unjudgeable\n";
/// What a row's command is, after `python3`.
const ALPHA_ARGS: &str = "-B scripts/land_gate.py validation-tests scripts.tests.alpha_test";
const BETA_ARGS: &str = "-B scripts/land_gate.py validation-tests scripts.tests.beta_test";
/// The files of the base table's two rows and two `[[not_run]]` entries.
const MODULES: [&str; 4] = [
    "scripts/tests/alpha_test.py",
    "scripts/tests/beta_test.py",
    "scripts/tests/delta_test.py",
    "scripts/tests/gamma_test.py",
];
/// The Git programs `controlled_git` runs, then the usual ones.
const GIT: [&str; 4] = [
    "/Library/Developer/CommandLineTools/usr/bin/git",
    "/Applications/Xcode.app/Contents/Developer/usr/bin/git",
    "/usr/bin/git",
    "/bin/git",
];

/// The stand-in for `python3`. `$4` is the module (`scripts.tests.<name>`);
/// `ends/<name>`, when the test wrote one, is shell that says how it ends.
const PYTHON3: &str = "#!/bin/sh\n\
     printf '%s|%s\\n' \"$(pwd -P)\" \"$*\" >> \"$LAND_CLI_WORLD/ran.log\"\n\
     ends=\"$LAND_CLI_WORLD/ends/${4##*.}\"\n\
     [ -f \"$ends\" ] && . \"$ends\"\n\
     exit 0\n";

/// The conformance fixture's base table: `validation.alpha_test` is selected
/// by `scripts/alpha.py`, and `validation.beta_test` by that and by `x.py`.
fn base_table() -> String {
    let fixture: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/land_select_cases.json")).unwrap();
    fixture["base_table"].as_str().unwrap().to_owned()
}

/// A directory holding a repository (`repo`) with a row table and the files
/// its rows name, committed; the stand-in `python3` (`bin`); how each module
/// ends (`ends`); what ran (`ran.log`); and the verb's temporary files (`tmp`).
struct World {
    root: tempfile::TempDir,
}

impl World {
    fn new() -> Self {
        Self::with_table(&base_table())
    }

    fn with_table(table: &str) -> Self {
        let world = Self { root: tempfile::tempdir().unwrap() };
        for directory in ["bin", "ends", "tmp", "repo"] {
            fs::create_dir_all(world.path(directory)).unwrap();
        }
        let python3 = world.path("bin/python3");
        fs::write(&python3, PYTHON3).unwrap();
        fs::set_permissions(&python3, fs::Permissions::from_mode(0o755)).unwrap();
        world.git(&["init", "--quiet", "--initial-branch=main"]);
        world.write("gates/land.toml", table);
        for file in MODULES.into_iter().chain(["scripts/alpha.py", "x.py"]) {
            world.write(file, "");
        }
        world.git(&["add", "--all"]);
        world.git(&["commit", "--quiet", "-m", "table"]);
        world
    }

    fn path(&self, relative: &str) -> PathBuf {
        self.root.path().join(relative)
    }

    /// The repository's root, resolved: where the verb runs a row's command.
    fn repo(&self) -> PathBuf {
        fs::canonicalize(self.path("repo")).unwrap()
    }

    /// Write a file of the repository.
    fn write(&self, relative: &str, text: &str) {
        let path = self.path("repo").join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    fn git(&self, args: &[&str]) -> String {
        let git = GIT.into_iter().find(|git| Path::new(git).is_file()).expect("a git");
        let output = Command::new(git)
            .env_clear()
            .env("LC_ALL", "C")
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .arg("-C")
            .arg(self.path("repo"))
            .args(["-c", "user.name=Trust Tests", "-c", "user.email=tests@example.invalid"])
            .args(args)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap().trim().to_owned()
    }

    /// Say how module `name`'s command ends: `script` is shell the stand-in
    /// runs. A module no test names exits 0.
    fn ends(&self, name: &str, script: &str) {
        fs::write(self.path("ends").join(name), script).unwrap();
    }

    /// One line per command that ran: its directory, `|`, its arguments.
    fn ran(&self) -> Vec<String> {
        match fs::read_to_string(self.path("ran.log")) {
            Ok(text) => text.lines().map(str::to_owned).collect(),
            Err(_) => Vec::new(),
        }
    }

    /// `targo trust land` with `args`, from `cwd`, with the stand-in first on
    /// its `PATH`.
    fn verb(&self, cwd: &Path, args: &[&str]) -> Command {
        let mut search = vec![self.path("bin")];
        search.extend(std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()));
        let mut command = Command::new(env!("CARGO_BIN_EXE_targo-trust"));
        command
            .args(["trust", "land"])
            .args(args)
            .current_dir(cwd)
            .env("PATH", std::env::join_paths(search).unwrap())
            .env("LAND_CLI_WORLD", self.root.path())
            .env("TMPDIR", self.path("tmp"))
            .stdin(Stdio::null());
        command
    }

    /// The verb from the repository's root.
    fn land(&self, args: &[&str]) -> Run {
        Run::of(self.verb(&self.path("repo"), args).output().unwrap())
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

    /// The file a row's line names as its log.
    fn log_of(&self, text: &str, id: &str) -> PathBuf {
        let line = text
            .lines()
            .find(|line| line.contains(&format!(" {id}: ")))
            .unwrap_or_else(|| panic!("no line of {id}:\n{}", self.all()));
        let (_, rest) = line.split_once("log: ").unwrap_or_else(|| panic!("no log in {line:?}"));
        let end = rest.find([')', ';']).unwrap_or_else(|| panic!("no end of the log in {line:?}"));
        PathBuf::from(&rest[..end])
    }
}

/// A row's line of the report: its verdict's word, then the rest.
fn row(word: &str, rest: &str) -> String {
    format!("{word:<11} {rest}\n")
}

/// The line the verb prints on stderr as it starts a row.
fn started(id: &str, position: &str, seconds: &str, args: &str) -> String {
    format!("land --check: {id} ({position}), at most {seconds}s: python3 {args}\n")
}

/// Wait for process `pid` to be gone.
fn gone(pid: i32) {
    let deadline = Instant::now() + Duration::from_secs(60);
    // SAFETY: signal 0 sends nothing; it only asks whether the pid is there.
    while unsafe { libc::kill(pid, 0) } == 0 {
        assert!(Instant::now() < deadline, "process {pid} is still running");
        std::thread::sleep(Duration::from_millis(20));
    }
}

#[test]
fn a_change_whose_rows_pass_is_exit_0_with_the_report_on_stdout() {
    let world = World::new();
    // Nothing changed: no row is selected, and that is exit 0 on stdout.
    let run = world.land(&["--check", "--base", "HEAD"]);
    assert_eq!(run.code, 0, "{}", run.all());
    assert!(run.stdout.contains("\nselected: 0 of 2 rows: nothing changed\n"), "{}", run.all());
    assert!(run.stdout.contains(&format!("\n{COUNTS}not judged here: ")), "{}", run.all());
    assert!(run.stdout.ends_with(&format!("\n{FOOTER}\n")), "{}", run.all());
    assert_eq!(run.stderr, "", "{}", run.all());
    assert!(world.ran().is_empty(), "no row ran");

    // A change to `x.py` selects one row; its command runs from the root.
    world.write("x.py", "changed\n");
    let run = world.land(&["--check", "--base", "HEAD"]);
    assert_eq!(run.code, 0, "{}", run.all());
    assert!(run.stdout.starts_with("land --check: base HEAD ("), "{}", run.all());
    let report = format!(
        "\nchanged: 1 path(s) (0 between the merge base and HEAD, 1 staged, changed in the \
         working tree or untracked)\nselected: 1 of 2 rows\n{}land --check: 1 PASS, 0 FAIL, 0 \
         NOT JUDGED of 1 selected row(s)\n{COUNTS}not judged here: ",
        row("PASS", "validation.beta_test")
    );
    assert!(run.stdout.contains(&report), "{}", run.all());
    assert!(run.stdout.ends_with(&format!("\n{FOOTER}\n")), "{}", run.all());
    assert_eq!(run.stderr, started("validation.beta_test", "1 of 1", "900", BETA_ARGS));
    let from_root = format!("{}|{BETA_ARGS}", world.repo().display());
    assert_eq!(world.ran(), [from_root.clone()]);

    // From a directory under the root, without --repo-root: the same table,
    // and the command still runs from the root.
    let under = world.path("repo/scripts/tests");
    let run = Run::of(world.verb(&under, &["--check", "--base=HEAD"]).output().unwrap());
    assert_eq!(run.code, 0, "{}", run.all());
    assert!(run.stdout.contains(&report), "{}", run.all());
    assert_eq!(world.ran(), [from_root.clone(), from_root]);
}

#[test]
fn a_row_that_fails_is_exit_1_with_the_report_on_stdout() {
    let world = World::new();
    world.write("scripts/alpha.py", "changed\n");
    world.ends("alpha_test", "echo alpha says no; echo and why >&2; exit 1");
    let run = world.land(&["--check", "--base", "HEAD"]);
    assert_eq!(run.code, 1, "{}", run.all());
    assert!(run.stdout.contains("FAIL        validation.alpha_test: exit 1 (log: "));
    let tally = format!(
        "{}land --check: 1 PASS, 1 FAIL, 0 NOT JUDGED of 2 selected row(s)\n{COUNTS}",
        row("PASS", "validation.beta_test")
    );
    assert!(run.stdout.contains(&tally), "{}", run.all());
    assert!(run.stdout.ends_with(&format!("\n{FOOTER}\n")), "{}", run.all());
    assert!(!run.stdout.contains("COULD NOT RUN"), "{}", run.all());
    // Both rows ran, in id order, and stderr holds their two lines only.
    assert_eq!(
        run.stderr,
        started("validation.alpha_test", "1 of 2", "900", ALPHA_ARGS)
            + &started("validation.beta_test", "2 of 2", "900", BETA_ARGS),
        "{}",
        run.all()
    );
    assert_eq!(world.ran().len(), 2);
    // The line names the row's log, which outlives the run: the command's
    // stdout and stderr, together.
    let log = run.log_of(&run.stdout, "validation.alpha_test");
    assert!(log.starts_with(fs::canonicalize(world.path("tmp")).unwrap()), "{}", log.display());
    assert_eq!(fs::read_to_string(&log).unwrap(), "alpha says no\nand why\n");

    // A command a signal ends failed too.
    world.ends("alpha_test", "kill -KILL $$");
    let run = world.land(&["--check", "--base", "HEAD"]);
    assert_eq!(run.code, 1, "{}", run.all());
    assert!(run.stdout.contains("FAIL        validation.alpha_test: ended by signal 9 (log: "));
}

#[test]
fn a_row_not_judged_is_exit_3_with_the_report_on_stderr() {
    let world = World::new();
    world.write("scripts/alpha.py", "changed\n");
    // One row has no verdict and the other fails: 3 outranks 1.
    world.ends("alpha_test", "exit 2");
    world.ends("beta_test", "exit 1");
    let run = world.land(&["--check", "--base", "HEAD"]);
    assert_eq!(run.code, 3, "{}", run.all());
    assert_eq!(run.stdout, "", "{}", run.all());
    assert!(
        run.stderr.contains(
            "NOT JUDGED  validation.alpha_test: exit 2, the runner's \"no test ran\" (log: "
        ),
        "{}",
        run.all()
    );
    assert!(run.stderr.contains("FAIL        validation.beta_test: exit 1 (log: "));
    let tally = format!(
        "land --check: 0 PASS, 1 FAIL, 1 NOT JUDGED of 2 selected row(s)\nLAND-CHECK: COULD NOT \
         RUN — 1 selected row(s) had no verdict, so the change is not judged\n{COUNTS}"
    );
    assert!(run.stderr.contains(&tally), "{}", run.all());
    assert!(run.stderr.ends_with(&format!("\n{FOOTER}\n")), "{}", run.all());

    // The control for the stream and the code: the same change with the
    // unjudged row passing is the failure alone, exit 1, on stdout.
    world.ends("alpha_test", "exit 0");
    let run = world.land(&["--check", "--base", "HEAD"]);
    assert_eq!(run.code, 1, "{}", run.all());
    assert!(run.stdout.contains("land --check: 1 PASS, 1 FAIL, 0 NOT JUDGED of 2 selected"));
}

#[test]
fn a_row_past_its_bound_is_stopped_and_not_judged_and_a_bound_past_the_clock_is_none() {
    let world = World::new();
    world.write("x.py", "changed\n");
    let pid_file = world.path("row.pid");
    world.ends("beta_test", &format!("echo $$ > '{}'; exec sleep 300", pid_file.display()));
    let run = world.land(&["--check", "--base", "HEAD", "--row-seconds", "2"]);
    assert_eq!(run.code, 3, "{}", run.all());
    assert_eq!(run.stdout, "", "{}", run.all());
    assert!(
        run.stderr.contains(
            "NOT JUDGED  validation.beta_test: no verdict within 2s (--row-seconds raises the \
             bound; log: "
        ),
        "{}",
        run.all()
    );
    assert!(run.stderr.contains(&format!("; rerun: python3 {BETA_ARGS}\n")), "{}", run.all());
    // The command was stopped, not left running.
    gone(fs::read_to_string(&pid_file).unwrap().trim().parse().unwrap());

    // The largest number of seconds there is: no deadline, and no overflow.
    // The row takes long enough for the verb to look at its clock.
    world.ends("beta_test", "sleep 1");
    let most = u64::MAX.to_string();
    let run = world.land(&["--check", "--base", "HEAD", "--row-seconds", &most]);
    assert_eq!(run.code, 0, "{}", run.all());
    assert!(run.stdout.contains(&row("PASS", "validation.beta_test")), "{}", run.all());
    assert_eq!(run.stderr, started("validation.beta_test", "1 of 1", &most, BETA_ARGS));
}

#[test]
fn a_usage_error_and_a_table_that_does_not_load_are_exit_2_on_stderr() {
    let world = World::new();
    world.write("x.py", "changed\n");
    // `land` without --check is the landing, which is not in Targo.
    let run = world.land(&[]);
    assert_eq!(run.code, 2, "{}", run.all());
    assert_eq!(run.stdout, "", "{}", run.all());
    assert!(
        run.stderr.starts_with("targo trust land: the landing is not implemented in Targo yet"),
        "{}",
        run.all()
    );
    assert!(run.stderr.contains("Usage: targo trust land --check") && run.stderr.contains(FOOTER));
    let run = world.land(&["--check", "--bogus"]);
    assert_eq!(run.code, 2, "{}", run.all());
    assert!(run.stderr.starts_with("targo trust land: unknown argument \"--bogus\""));
    assert_eq!(run.stdout, "", "{}", run.all());
    // A checkout that is not there.
    let run = world.land(&["--check", "--repo-root", "no-such-directory"]);
    assert_eq!(run.code, 2, "{}", run.all());
    assert!(run.stderr.starts_with("targo trust land: no checkout at "), "{}", run.all());
    assert!(run.stderr.ends_with(&format!("\n{FOOTER}\n")), "{}", run.all());
    assert!(!run.stderr.contains("rows are not yet"), "{}", run.all());

    // A tree that breaks the table's `covered` rule, once git tracks the file.
    world.write("scripts/tests/zz_new_test.py", "");
    world.git(&["add", "scripts/tests/zz_new_test.py"]);
    let run = world.land(&["--check", "--base", "HEAD"]);
    assert_eq!(run.code, 2, "{}", run.all());
    assert_eq!(run.stdout, "", "{}", run.all());
    assert!(
        run.stderr
            .starts_with("targo trust land: gates/land.toml: 1 file(s) break its `covered` rule"),
        "{}",
        run.all()
    );
    let named =
        format!("\n  scripts/tests/zz_new_test.py: neither a [[row]] nor a [[not_run]]\n{COUNTS}");
    assert!(run.stderr.contains(&named), "{}", run.all());
    assert!(run.stderr.ends_with(&format!("\n{FOOTER}\n")), "{}", run.all());
    assert!(world.ran().is_empty(), "no row ran in any of these");

    // A table of another schema: refused whole, with no rows to count.
    let other = World::with_table(&base_table().replace("land-rows.v1", "land-rows.v2"));
    other.write("x.py", "changed\n");
    let run = other.land(&["--check", "--base", "HEAD"]);
    assert_eq!(run.code, 2, "{}", run.all());
    assert_eq!(run.stdout, "", "{}", run.all());
    assert_eq!(
        run.stderr,
        format!(
            "targo trust land: gates/land.toml: schema is \"trust.land-rows.v2\"; this reader \
             knows \"trust.land-rows.v1\"\n{FOOTER}\n"
        )
    );
    assert!(other.ran().is_empty());
}

#[test]
fn a_change_git_cannot_show_is_exit_3_on_stderr_and_never_no_change() {
    let world = World::new();
    world.write("x.py", "changed\n");
    // The default base is origin/main, which this repository does not have.
    let run = world.land(&["--check"]);
    assert_eq!(run.code, 3, "{}", run.all());
    assert_eq!(run.stdout, "", "{}", run.all());
    assert!(
        run.stderr.starts_with(
            "LAND-CHECK: COULD NOT RUN — the base \"origin/main\" does not resolve to a commit"
        ),
        "{}",
        run.all()
    );
    assert!(run.stderr.contains(&format!("\n{COUNTS}not judged here: ")), "{}", run.all());
    assert!(run.stderr.ends_with(&format!("\n{FOOTER}\n")), "{}", run.all());

    // An index entry git does not compare with the working tree.
    for (mark, clear) in
        [("--assume-unchanged", "--no-assume-unchanged"), ("--skip-worktree", "--no-skip-worktree")]
    {
        world.git(&["update-index", mark, "x.py"]);
        assert_eq!(world.git(&["status", "--porcelain"]), "", "{mark}: git shows no change");
        let run = world.land(&["--check", "--base", "HEAD"]);
        assert_eq!(run.code, 3, "{mark}: {}", run.all());
        assert_eq!(run.stdout, "", "{mark}: {}", run.all());
        assert!(
            run.stderr.starts_with(
                "LAND-CHECK: COULD NOT RUN — 1 index entry is marked assume-unchanged or \
                 skip-worktree (x.py): "
            ),
            "{mark}: {}",
            run.all()
        );
        assert!(!run.stderr.contains("selected:"), "{mark}: {}", run.all());
        assert!(run.stderr.ends_with(&format!("\n{FOOTER}\n")), "{mark}: {}", run.all());
        world.git(&["update-index", clear, "x.py"]);
    }
    assert!(world.ran().is_empty(), "no row ran in any of these");

    // The control: the same tree with no mark is a change, and its row runs.
    let run = world.land(&["--check", "--base", "HEAD"]);
    assert_eq!(run.code, 0, "{}", run.all());
    assert!(run.stdout.contains(&row("PASS", "validation.beta_test")), "{}", run.all());
    assert_eq!(world.ran().len(), 1);

    // An index git cannot read at all.
    fs::write(world.path("repo/.git/index"), "not an index").unwrap();
    let run = world.land(&["--check", "--base", "HEAD"]);
    assert_eq!(run.code, 3, "{}", run.all());
    assert!(
        run.stderr
            .starts_with("LAND-CHECK: COULD NOT RUN — the tracked files: git ls-files exited "),
        "{}",
        run.all()
    );
    assert_eq!(run.stdout, "", "{}", run.all());
}

#[test]
fn help_is_exit_0_on_stdout() {
    let world = World::new();
    for flag in ["--help", "-h"] {
        let run = world.land(&[flag]);
        assert_eq!(run.code, 0, "{}", run.all());
        assert!(run.stdout.starts_with("Usage: targo trust land --check [--base REV]"));
        assert!(run.stdout.contains(FOOTER), "{}", run.all());
        assert_eq!(run.stderr, "", "{}", run.all());
    }
}

#[test]
fn a_signal_to_the_verb_stops_the_row_and_is_exit_3() {
    let world = World::new();
    world.write("x.py", "changed\n");
    let pid_file = world.path("row.pid");
    world.ends("beta_test", &format!("echo $$ > '{}'; exec sleep 300", pid_file.display()));
    let mut command = world.verb(&world.path("repo"), &["--check", "--base", "HEAD"]);
    let verb = command.stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    // Wait for the row's command to be running.
    let deadline = Instant::now() + Duration::from_secs(120);
    let row_pid: i32 = loop {
        if let Some(pid) =
            fs::read_to_string(&pid_file).ok().and_then(|text| text.trim().parse().ok())
        {
            break pid;
        }
        assert!(Instant::now() < deadline, "the row's command did not start");
        std::thread::sleep(Duration::from_millis(20));
    };
    let verb_pid = i32::try_from(verb.id()).unwrap();
    // SAFETY: the pid is this test's own child, which it has not waited for.
    assert_eq!(unsafe { libc::kill(verb_pid, libc::SIGTERM) }, 0);
    let run = Run::of(verb.wait_with_output().unwrap());
    assert_eq!(run.code, 3, "{}", run.all());
    assert_eq!(run.stdout, "", "a stopped run reports no verdict:\n{}", run.all());
    assert!(!run.stderr.contains("PASS") && !run.stderr.contains("FAIL"), "{}", run.all());
    let last = run.stderr.lines().last().unwrap_or_default();
    assert!(last.contains("COULD NOT RUN") && last.contains("interrupted by SIGTERM"), "{last}");
    gone(row_pid);
}
