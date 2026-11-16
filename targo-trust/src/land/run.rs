//! One row's command: the process, its bound, its log, and its verdict.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use crate::logged_child::{self, ChildExit};

/// The exit of `scripts/land_gate.py validation-tests` when a module holds no
/// test, or ran none that was not skipped: the row command's "no test ran".
const NO_TEST_RAN: i32 = 2;

/// One row, as the verb hands it to a [`RowRunner`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RowSpec {
    pub(crate) id: String,
    /// The row's command, from the table.
    pub(crate) argv: Vec<String>,
    /// The checkout's root: the command's working directory.
    pub(crate) root: PathBuf,
    /// Where the command's stdout and stderr go, together.
    pub(crate) log: PathBuf,
    /// How long the command may take.
    pub(crate) bound: Duration,
}

/// What runs a row's command. The verb's is [`RowProcess`]; the verb's tests
/// also stand in a runner that only answers (`land/tests.rs`).
pub(crate) trait RowRunner {
    fn run(&mut self, spec: &RowSpec) -> ChildExit;
}

/// The command as an owned child (`logged_child`): no stdin, its output in the
/// row's log, stopped with its process group at the bound or when a signal
/// stops the verb. It inherits the verb's environment, as the Python gate's
/// validation leg inherits the gate's.
pub(crate) struct RowProcess;

impl RowRunner for RowProcess {
    fn run(&mut self, spec: &RowSpec) -> ChildExit {
        let Some((program, arguments)) = spec.argv.split_first() else {
            return ChildExit::Failed("the row has no command".into());
        };
        let mut command = Command::new(program);
        command.args(arguments).current_dir(&spec.root);
        logged_child::run_logged(&mut command, &spec.log, spec.bound, "the row's command")
    }
}

/// What a row's run says of the row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Verdict {
    Pass,
    /// The command ran and did not pass: why.
    Fail(String),
    /// Nothing judged the row: why.
    NotJudged(String),
}

impl Verdict {
    pub(crate) fn word(&self) -> &'static str {
        match self {
            Self::Pass => "PASS",
            Self::Fail(_) => "FAIL",
            Self::NotJudged(_) => "NOT JUDGED",
        }
    }
}

/// The verdict of a row whose command ended as `exit`. Exit 0 is the only
/// PASS. Exit 2 is the runner's "no test ran" and a command still running at
/// its bound gave no verdict: neither is a FAIL, and neither is ever a PASS. A
/// command that was killed, or left with any other status, failed.
pub(crate) fn judge(spec: &RowSpec, exit: &ChildExit) -> Verdict {
    let log = spec.log.display();
    match exit {
        ChildExit::Exited(0) => Verdict::Pass,
        ChildExit::Exited(NO_TEST_RAN) => Verdict::NotJudged(format!(
            "exit {NO_TEST_RAN}, the runner's \"no test ran\" (log: {log})"
        )),
        ChildExit::Exited(code) => Verdict::Fail(format!("exit {code} (log: {log})")),
        ChildExit::Signalled(signal) => {
            Verdict::Fail(format!("ended by signal {signal} (log: {log})"))
        }
        ChildExit::PastBound => Verdict::NotJudged(format!(
            "no verdict within {}s (--row-seconds raises the bound; log: {log}); rerun: {}",
            spec.bound.as_secs(),
            command_line(&spec.argv)
        )),
        ChildExit::Failed(error) => Verdict::NotJudged(error.clone()),
    }
}

/// An argv as a line a shell reads back as that argv.
pub(crate) fn command_line(argv: &[String]) -> String {
    argv.iter().map(|part| shell_word(part)).collect::<Vec<_>>().join(" ")
}

fn shell_word(part: &str) -> String {
    let plain = |c: char| c.is_ascii_alphanumeric() || "_-./=:,+@%".contains(c);
    if !part.is_empty() && part.chars().all(plain) {
        return part.to_owned();
    }
    format!("'{}'", part.replace('\'', "'\\''"))
}

/// The log of row `id` under `logs`: a row id is a file name.
pub(crate) fn log_path(logs: &Path, id: &str) -> PathBuf {
    logs.join(format!("{id}.log"))
}
