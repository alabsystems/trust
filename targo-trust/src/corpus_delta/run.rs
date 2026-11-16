//! One compile of one case: the process, its bound, and its log.

use std::fs::File;
use std::io::{self, BufRead, BufReader, Read};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use crate::bounded_process;
use crate::process_lifecycle::{self, StopCause};

/// What no compiler under comparison inherits: with either set, a compiler
/// joins the host's trustd, and its verdicts depend on what else the host runs.
pub(crate) const SCRUBBED_ENV: [&str; 2] =
    ["TRUST_MEMORY_JOBSERVER_SOCK", "TRUST_MEMORY_JOBSERVER"];

/// How much of a log is searched for its first `error` line.
const MAX_LOG_SCAN_BYTES: u64 = 64 * 1024 * 1024;
/// The longest cause a record keeps, in characters.
const MAX_CAUSE_CHARS: usize = 160;

/// One case, as the verb hands it to a [`CaseRunner`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CaseSpec {
    pub(crate) compiler: PathBuf,
    pub(crate) corpus: String,
    pub(crate) case: String,
    /// The row's arguments; the runner adds `--out-dir <work>` and the source.
    pub(crate) args: Vec<String>,
    pub(crate) source: PathBuf,
    /// The compiler's working directory and `--out-dir`: scratch, never the
    /// checkout.
    pub(crate) work: PathBuf,
    /// Where the compiler's stdout and stderr go, together.
    pub(crate) log: PathBuf,
    /// How long the compiler may take.
    pub(crate) bound: Duration,
}

/// How one compile ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CaseExit {
    Exited(i32),
    /// Ended by this signal (no exit status).
    Signalled(i32),
    /// Still running at its bound, and stopped.
    PastBound,
    /// Could not be started, or waited for.
    Failed(String),
}

/// What compiles a case. The verb's is [`CompilerProcess`]; the verb's tests
/// stand in a runner that writes logs (`corpus_delta/tests.rs`).
pub(crate) trait CaseRunner {
    /// How the compile ended; `None` when the runner made no record of the
    /// case, which the comparison then treats as not recorded by that side.
    fn run(&mut self, spec: &CaseSpec) -> Option<CaseExit>;
}

/// The compiler as an owned child (`process_lifecycle`): a signal to the verb
/// stops it, and what is left of its process group when its leader exits is
/// stopped before the leader is reaped.
pub(crate) struct CompilerProcess;

impl CaseRunner for CompilerProcess {
    fn run(&mut self, spec: &CaseSpec) -> Option<CaseExit> {
        let mut command = Command::new(&spec.compiler);
        command
            .args(&spec.args)
            .arg("--out-dir")
            .arg(&spec.work)
            .arg(&spec.source)
            .current_dir(&spec.work);
        Some(run_logged(&mut command, &spec.log, spec.bound))
    }
}

/// Run `command` to its end or to `bound`, with no stdin, its stdout and stderr
/// in `log`, and none of [`SCRUBBED_ENV`].
pub(super) fn run_logged(command: &mut Command, log: &Path, bound: Duration) -> CaseExit {
    let streams = File::create(log).and_then(|out| Ok((out.try_clone()?, out)));
    let (stdout, stderr) = match streams {
        Ok(streams) => streams,
        Err(error) => return CaseExit::Failed(format!("cannot create {}: {error}", log.display())),
    };
    command.stdin(Stdio::null()).stdout(stdout).stderr(stderr);
    for name in SCRUBBED_ENV {
        command.env_remove(name);
    }
    let (mut child, ownership) = match process_lifecycle::spawn_owned(command) {
        Ok(owned) => owned,
        Err(error) => {
            return CaseExit::Failed(format!(
                "cannot start {}: {error}",
                Path::new(command.get_program()).display()
            ));
        }
    };
    let exit = wait_within(&mut child, bound);
    drop(ownership);
    exit
}

/// `stability::legs::wait_then_sweep` with a bound: wait for the leader
/// without reaping it, stop what is left of its group while the unreaped
/// leader still reserves the group's id, then reap it. A leader still running
/// at `bound` is stopped with its group and has no exit.
fn wait_within(child: &mut Child, bound: Duration) -> CaseExit {
    const LONGEST_POLL: Duration = Duration::from_millis(50);
    let deadline = Instant::now() + bound;
    let mut poll = Duration::from_millis(1);
    loop {
        match bounded_process::exited_without_reaping(child) {
            Ok(true) => break,
            Ok(false) if Instant::now() < deadline => {
                std::thread::sleep(poll);
                poll = (poll * 2).min(LONGEST_POLL);
            }
            Ok(false) => {
                let _ = process_lifecycle::stop_child(child, StopCause::Bound);
                let _ = child.wait();
                return CaseExit::PastBound;
            }
            Err(error) => {
                let _ = process_lifecycle::stop_child(child, StopCause::Error);
                let _ = child.wait();
                return CaseExit::Failed(format!("cannot wait for the compiler: {error}"));
            }
        }
    }
    // A signal that stopped the verb may be why the compiler exited: its exit
    // is no verdict, and the stop owns the run's exit.
    process_lifecycle::signals::hold_if_interrupted();
    #[cfg(unix)]
    let _ = process_lifecycle::stop_tree(child.id(), StopCause::LeaderExited);
    match child.wait() {
        Ok(status) => exit_of(status),
        Err(error) => CaseExit::Failed(format!("cannot wait for the compiler: {error}")),
    }
}

fn exit_of(status: ExitStatus) -> CaseExit {
    if let Some(code) = status.code() {
        return CaseExit::Exited(code);
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt as _;
        if let Some(signal) = status.signal() {
            return CaseExit::Signalled(signal);
        }
    }
    CaseExit::Failed(format!("the compiler ended with neither a status nor a signal: {status}"))
}

/// The first line of `log` that starts with `error`, as a record's cause: at
/// most [`MAX_CAUSE_CHARS`] characters, a tab shown as a space. Empty when
/// there is none.
pub(crate) fn first_error_line(log: &Path) -> String {
    let Ok(file) = File::open(log) else {
        return String::new();
    };
    first_error_line_of(BufReader::new(file.take(MAX_LOG_SCAN_BYTES))).unwrap_or_default()
}

fn first_error_line_of(reader: impl BufRead) -> io::Result<String> {
    for line in reader.split(b'\n') {
        let line = line?;
        if line.starts_with(b"error") {
            return Ok(String::from_utf8_lossy(&line)
                .trim_end_matches('\r')
                .chars()
                .take(MAX_CAUSE_CHARS)
                .map(|c| if c == '\t' { ' ' } else { c })
                .collect());
        }
    }
    Ok(String::new())
}
