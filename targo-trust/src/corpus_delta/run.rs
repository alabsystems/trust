//! One compile of one case: the process, its bound, and its log.

use std::fs::File;
use std::io::{self, BufRead, BufReader, Read};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use crate::logged_child;

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
    /// Variables the row gives this compile.
    pub(crate) env: Vec<(String, String)>,
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
pub(crate) use crate::logged_child::ChildExit as CaseExit;

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
            .envs(spec.env.iter().map(|(name, value)| (name, value)))
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
    for name in SCRUBBED_ENV {
        command.env_remove(name);
    }
    logged_child::run_logged(command, log, bound, "the compiler")
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

/// Whether a line of `log` contains `needle`, as the corpus scripts'
/// `grep -qF -- <needle> <log>` answers. The whole log is read: a text that is
/// there is never reported absent because the log is long.
pub(crate) fn log_contains(log: &Path, needle: &str) -> io::Result<bool> {
    let needle = needle.as_bytes();
    if needle.is_empty() {
        return Ok(true);
    }
    for line in BufReader::new(File::open(log)?).split(b'\n') {
        if line?.windows(needle.len()).any(|window| window == needle) {
            return Ok(true);
        }
    }
    Ok(false)
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
