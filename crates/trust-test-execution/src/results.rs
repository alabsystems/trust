//! Per-case test results, carried apart from the tests' own output.
//!
//! A test binary's stdout and stderr belong to the tests: user code writes to
//! them as freely as libtest does, so nothing read from those streams can say
//! which case passed. The result channel is libtest's `--logfile <path>`
//! instead. Native Targo gives every harness of a prepared plan its own result
//! file, puts `--logfile <file>` first in that harness's sealed argument list
//! (so the frontend authenticates it with the rest of the plan), and, once the
//! harness process has ended, writes beside it how it ended ([`HarnessExit`]).
//!
//! First, not last: libtest reads its arguments with getopts, which stops
//! reading options at `--` and gives a value-taking option (`--skip`,
//! `--color`, ...) the next argument whatever it is. A channel after the
//! user's test arguments could be swallowed by them (`-- --` would turn it
//! into two name filters that match nothing, so a failing suite ran no case
//! and exited 0). Before every other argument nothing can reach it, and a
//! second `--logfile` is libtest's own error.
//! Libtest writes one line per finished case to the result file, separately
//! from the output streams:
//!
//! ```text
//! ok <name>
//! failed <name>
//! failed: <message> <name>
//! ignored <name>
//! ignored: <reason> <name>
//! ```
//!
//! `--logfile` is a stable libtest option (deprecated upstream, so libtest
//! prints one warning line on stderr; it is still accepted). The JSON event
//! format would also carry a case count, but it needs `-Z unstable-options`,
//! which a test binary may refuse. Neither file is proof of anything: the
//! harness is linked into the user's program, and the user's code can write
//! these files as freely as libtest does. A reader states every outcome as
//! reported by the test binary's own harness and raises no verdict from it.
//!
//! Nothing here judges the result file. The reader (`targo-trust`) holds the
//! fail-closed rules: a missing, truncated or unreadable file, a missing exit
//! record, or a file that disagrees with how the harness ended is not
//! concluded, never passed.

use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

/// The schema of a harness exit record.
pub const HARNESS_EXIT_SCHEMA: &str = "targo.test-harness-exit.v1";
/// The directory, beside the prepared plan, that holds every result file.
pub const RESULTS_DIR: &str = "test-results";
/// The libtest option that names a harness's result file.
pub const LOGFILE_FLAG: &str = "--logfile";
/// The largest result file a reader accepts.
pub const MAX_LOGFILE_BYTES: u64 = 16 * 1024 * 1024;
/// The largest exit record a reader accepts.
pub const MAX_EXIT_RECORD_BYTES: u64 = 64 * 1024;

/// Where one harness's results go: libtest's result file and the exit record
/// native Targo writes after the harness ends.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HarnessResultFiles {
    pub logfile: String,
    pub exit: String,
}

impl HarnessResultFiles {
    /// The files of the `index`-th harness of a plan exported to `plan_path`:
    /// `<plan dir>/test-results/<index>.libtest` and `<index>.exit`.
    pub fn for_harness(plan_path: &Path, index: usize) -> Result<Self, String> {
        let dir = results_dir(plan_path)?;
        let utf8 = |path: PathBuf| {
            path.into_os_string()
                .into_string()
                .map_err(|_| "test result paths must be UTF-8".to_string())
        };
        Ok(Self {
            logfile: utf8(dir.join(format!("{index}.libtest")))?,
            exit: utf8(dir.join(format!("{index}.exit")))?,
        })
    }

    /// The two arguments that name the result file to libtest.
    pub fn libtest_args(&self) -> [String; 2] {
        [LOGFILE_FLAG.to_string(), self.logfile.clone()]
    }

    /// A harness's arguments: the result channel first, then `test_args`
    /// (module docs: nothing after the channel can swallow it).
    pub fn harness_args<S: AsRef<str>>(&self, test_args: &[S]) -> Vec<String> {
        self.libtest_args()
            .into_iter()
            .chain(test_args.iter().map(|arg| arg.as_ref().to_string()))
            .collect()
    }
}

/// `<plan dir>/test-results` for a plan exported to `plan_path`.
pub fn results_dir(plan_path: &Path) -> Result<PathBuf, String> {
    if !plan_path.is_absolute() {
        return Err("a prepared plan path must be absolute".into());
    }
    let parent = plan_path.parent().ok_or("a prepared plan path has no directory")?;
    Ok(parent.join(RESULTS_DIR))
}

/// Create the private results directory of a plan exported to `plan_path`.
pub fn create_results_dir(plan_path: &Path) -> std::io::Result<PathBuf> {
    let dir = results_dir(plan_path).map_err(std::io::Error::other)?;
    let mut builder = std::fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder.create(&dir)?;
    Ok(dir)
}

/// Whether `arg` names a libtest result file.
pub fn is_logfile_arg(arg: &str) -> bool {
    arg == LOGFILE_FLAG || arg.starts_with("--logfile=")
}

/// How a harness process ended, as native Targo observed it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields, tag = "ended", rename_all = "kebab-case")]
pub enum HarnessEnd {
    /// The process exited with this status code.
    Exited { code: i32 },
    /// A signal ended the process.
    Signaled { signal: i32 },
    /// No exit was observed: the harness was refused before or after it ran,
    /// cancelled, or could not be waited for.
    NotObserved { reason: String },
}

/// The record native Targo writes after a harness ends.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HarnessExit {
    pub schema: String,
    pub session: String,
    pub executable: String,
    pub sha256: String,
    pub logfile: String,
    pub end: HarnessEnd,
}

fn open_private_new(path: &Path) -> std::io::Result<std::fs::File> {
    let mut options = std::fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600).custom_flags(libc::O_NOFOLLOW);
    }
    options.open(path)
}

/// Write `exit` to `path`, which must not exist yet.
pub fn write_exit(path: &Path, exit: &HarnessExit) -> std::io::Result<()> {
    let bytes = serde_json::to_vec(exit).map_err(std::io::Error::other)?;
    let mut file = open_private_new(path)?;
    file.write_all(&bytes)?;
    file.sync_all()
}

/// Read a regular file at `path`, never through a symbolic link, refusing one
/// larger than `limit`.
pub fn read_bounded(path: &Path, limit: u64) -> Result<Vec<u8>, String> {
    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        // An untrusted harness may leave a FIFO with no writer. Open without
        // waiting, then inspect this same descriptor before reading anything.
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let file = options.open(path).map_err(|error| format!("cannot open: {error}"))?;
    let metadata = file.metadata().map_err(|error| format!("cannot inspect: {error}"))?;
    if !metadata.is_file() {
        return Err("not a regular file".into());
    }
    let mut bytes = Vec::new();
    file.take(limit + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("cannot read: {error}"))?;
    if bytes.len() as u64 > limit {
        return Err(format!("larger than {limit} bytes"));
    }
    Ok(bytes)
}

/// Read the exit record at `path`.
pub fn read_exit(path: &Path) -> Result<HarnessExit, String> {
    let bytes = read_bounded(path, MAX_EXIT_RECORD_BYTES)?;
    let exit: HarnessExit =
        serde_json::from_slice(&bytes).map_err(|error| format!("not an exit record: {error}"))?;
    if exit.schema != HARNESS_EXIT_SCHEMA {
        return Err(format!("schema `{}`, not `{HARNESS_EXIT_SCHEMA}`", exit.schema));
    }
    Ok(exit)
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    #[test]
    fn each_harness_gets_its_own_files_beside_the_plan() {
        let plan = Path::new("/session/prepared-tests.json");
        let first = HarnessResultFiles::for_harness(plan, 0).unwrap();
        let second = HarnessResultFiles::for_harness(plan, 1).unwrap();
        assert_eq!(first.logfile, "/session/test-results/0.libtest");
        assert_eq!(first.exit, "/session/test-results/0.exit");
        assert_ne!(first.logfile, second.logfile);
        assert_eq!(first.libtest_args(), ["--logfile", "/session/test-results/0.libtest"]);
        assert_eq!(
            first.harness_args(&["--", "--skip"]),
            ["--logfile", "/session/test-results/0.libtest", "--", "--skip"]
        );
        assert!(HarnessResultFiles::for_harness(Path::new("relative.json"), 0).is_err());
    }

    #[test]
    fn an_exit_record_is_written_once_privately_and_read_back_exactly() {
        let root = std::env::temp_dir().join(format!(
            "trust-test-results-{}-{}",
            std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
        ));
        std::fs::create_dir_all(&root).unwrap();
        let plan = root.join("prepared-tests.json");
        let dir = create_results_dir(&plan).unwrap();
        let path = dir.join("0.exit");
        let exit = HarnessExit {
            schema: HARNESS_EXIT_SCHEMA.into(),
            session: "s".into(),
            executable: "/t/x".into(),
            sha256: "a".repeat(64),
            logfile: dir.join("0.libtest").display().to_string(),
            end: HarnessEnd::Signaled { signal: 6 },
        };
        write_exit(&path, &exit).unwrap();
        assert!(write_exit(&path, &exit).is_err(), "a second record never replaces the first");
        assert_eq!(read_exit(&path).unwrap(), exit);
        use std::os::unix::fs::PermissionsExt;
        assert_eq!(std::fs::metadata(&path).unwrap().permissions().mode() & 0o077, 0);
        std::fs::write(&path.with_extension("bad"), b"{\"schema\":\"other\"}").unwrap();
        assert!(read_exit(&path.with_extension("bad")).is_err());
        std::os::unix::fs::symlink(&path, dir.join("link.exit")).unwrap();
        assert!(read_exit(&dir.join("link.exit")).is_err(), "never read through a link");
        std::fs::remove_dir_all(&root).unwrap();
    }
}
