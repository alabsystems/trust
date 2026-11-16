//! Which compiler a side measured.
//!
//! A count about a compiler means nothing until it names the compiler. On m21
//! on 2026-11-12 an unargued corpus run took a 2026-09-28 `build/` compiler
//! while ALab ran pack 16387: it measured neither the checkout nor the deployed
//! toolchain, and its output could not say which. So a side is a path the
//! caller wrote, never a compiler looked up on `PATH` or under `build/`; it
//! must be a regular executable file that answers `-vV`; and the report prints
//! the release line and commit it answered with, and says when that commit is
//! not the checkout's HEAD.

use std::fs::{self, File};
use std::io::Read;
use std::path::Path;
use std::process::Command;
use std::time::Duration;

use super::run::{self, CaseExit};
use crate::controlled_git;

/// How long `-vV` may take: a hang detector, not a budget.
const VERSION_BOUND: Duration = Duration::from_secs(600);
/// How much of `-vV`'s output is read.
const MAX_VERSION_BYTES: u64 = 64 * 1024;
/// How many lines of a failed `-vV` the refusal shows.
const SHOWN_FAILURE_LINES: usize = 3;
/// A commit as the report abbreviates it.
const SHORT_COMMIT_CHARS: usize = 10;

/// A compiler's `-vV`: how it ended and what it printed (stdout and stderr).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct VersionProbe {
    pub(crate) exit: CaseExit,
    pub(crate) output: String,
}

/// What the verb asks about a compiler and the checkout. The verb's is
/// [`ProcessProbe`]; its tests stand in fixed answers.
pub(crate) trait CompilerProbe {
    /// Run `<compiler> -vV`, its output going to `log`.
    fn verbose_version(&mut self, compiler: &Path, log: &Path) -> VersionProbe;
    /// The checkout's HEAD commit, where it has one.
    fn checkout_head(&mut self, root: &Path) -> Option<String>;
}

pub(crate) struct ProcessProbe;

impl CompilerProbe for ProcessProbe {
    fn verbose_version(&mut self, compiler: &Path, log: &Path) -> VersionProbe {
        let mut command = Command::new(compiler);
        command.arg("-vV");
        let exit = run::run_logged(&mut command, log, VERSION_BOUND);
        let mut bytes = Vec::new();
        if let Ok(file) = File::open(log) {
            let _ = file.take(MAX_VERSION_BYTES).read_to_end(&mut bytes);
        }
        VersionProbe { exit, output: String::from_utf8_lossy(&bytes).into_owned() }
    }

    fn checkout_head(&mut self, root: &Path) -> Option<String> {
        controlled_git::canonical_head(
            root,
            "corpus-delta checkout HEAD",
            64 * 1024,
            Duration::from_secs(30),
        )
        .ok()
    }
}

/// Whether `path` is a regular file with an execute bit: a directory, a
/// missing path and a plain data file are not compilers.
pub(crate) fn is_executable_file(path: &Path) -> bool {
    let Ok(metadata) = fs::metadata(path) else {
        return false;
    };
    if !metadata.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        true
    }
}

/// What a compiler says it is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Identity {
    /// The first line of `-vV`.
    pub(crate) release: String,
    /// Its `commit-hash`, unless absent or `unknown`.
    pub(crate) commit: Option<String>,
    pub(crate) date: Option<String>,
}

impl Identity {
    pub(crate) fn parse(output: &str) -> Self {
        let field = |name: &str| {
            output
                .lines()
                .find_map(|line| line.strip_prefix(name))
                .map(str::trim)
                .filter(|value| !value.is_empty() && *value != "unknown")
                .map(str::to_owned)
        };
        Self {
            release: output.lines().next().unwrap_or_default().trim_end().to_owned(),
            commit: field("commit-hash: "),
            date: field("commit-date: "),
        }
    }

    /// `<release> | <commit> <date>`.
    pub(crate) fn headline(&self) -> String {
        let mut line =
            format!("{} | {}", self.release, self.commit.as_deref().unwrap_or("unknown"));
        if let Some(date) = &self.date {
            line.push(' ');
            line.push_str(date);
        }
        line
    }

    /// What a reader must know before tying this side's counts to a tree.
    pub(crate) fn note(&self, side: &str, head: Option<&str>) -> Option<String> {
        let short = |commit: &str| commit.chars().take(SHORT_COMMIT_CHARS).collect::<String>();
        match (&self.commit, head) {
            (None, _) => Some(format!(
                "NOTE: the {side} compiler names no commit, so its counts cannot be tied to a tree"
            )),
            (Some(commit), Some(head)) if commit != head => Some(format!(
                "NOTE: the {side} compiler was built from {}, not this checkout's HEAD {}",
                short(commit),
                short(head)
            )),
            _ => None,
        }
    }
}

/// Ask `compiler` what it is. A compiler that cannot report its own version
/// would "refuse" every case, so it is refused before any case runs.
pub(crate) fn identify(
    probe: &mut dyn CompilerProbe,
    compiler: &Path,
    log: &Path,
) -> Result<Identity, String> {
    let VersionProbe { exit, output } = probe.verbose_version(compiler, log);
    let ended = match exit {
        CaseExit::Exited(0) => return Ok(Identity::parse(&output)),
        CaseExit::Exited(code) => format!("`-vV` exited {code}"),
        CaseExit::Signalled(signal) => format!("`-vV` was ended by signal {signal}"),
        CaseExit::PastBound => {
            format!("`-vV` did not finish within {}s", VERSION_BOUND.as_secs())
        }
        CaseExit::Failed(error) => error,
    };
    let mut refusal = format!("the compiler at {} does not run: {ended}", compiler.display());
    for line in output.lines().take(SHOWN_FAILURE_LINES) {
        refusal.push_str("\n  ");
        refusal.push_str(line);
    }
    Err(refusal)
}
