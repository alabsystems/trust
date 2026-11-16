use std::ffi::{OsStr, OsString};
use std::path::PathBuf;
use std::process::Command;
use std::str;

/// This macro creates the version string during compilation from the
/// current environment
#[macro_export]
macro_rules! get_version_info {
    () => {{
        let major = std::env!("CARGO_PKG_VERSION_MAJOR").parse::<u8>().unwrap();
        let minor = std::env!("CARGO_PKG_VERSION_MINOR").parse::<u8>().unwrap();
        let patch = std::env!("CARGO_PKG_VERSION_PATCH").parse::<u16>().unwrap();
        let crate_name = String::from(std::env!("CARGO_PKG_NAME"));

        let host_compiler = std::option_env!("RUSTC_RELEASE_CHANNEL").map(str::to_string);
        let commit_hash = std::option_env!("GIT_HASH").map(str::to_string);
        let commit_date = std::option_env!("COMMIT_DATE").map(str::to_string);

        $crate::VersionInfo {
            major,
            minor,
            patch,
            host_compiler,
            commit_hash,
            commit_date,
            crate_name,
        }
    }};
}

/// This macro can be used in `build.rs` to automatically set the needed environment values, namely
/// `GIT_HASH`, `COMMIT_DATE`  and `RUSTC_RELEASE_CHANNEL`
///
/// Trust: the commit is the one bootstrap's commit tuple names when bootstrap hands one
/// ([`get_bootstrap_commit_info`]), and git is then neither asked nor watched; otherwise it is
/// HEAD's, as upstream's.
#[macro_export]
macro_rules! setup_version_info {
    () => {{
        let (commit_hash, commit_date) = match $crate::get_bootstrap_commit_info() {
            Some(commit) => commit,
            None => {
                let _ = $crate::rerun_if_git_changes();
                (
                    $crate::get_commit_hash().unwrap_or_default(),
                    $crate::get_commit_date().unwrap_or_default(),
                )
            },
        };
        println!("cargo:rustc-env=GIT_HASH={}", commit_hash);
        println!("cargo:rustc-env=COMMIT_DATE={}", commit_date);
        let compiler_version = $crate::get_compiler_version();
        println!(
            "cargo:rustc-env=RUSTC_RELEASE_CHANNEL={}",
            $crate::get_channel(compiler_version)
        );
    }};
}

// some code taken and adapted from RLS and cargo
pub struct VersionInfo {
    pub major: u8,
    pub minor: u8,
    pub patch: u16,
    pub host_compiler: Option<String>,
    pub commit_hash: Option<String>,
    pub commit_date: Option<String>,
    pub crate_name: String,
}

impl std::fmt::Display for VersionInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let hash = self.commit_hash.clone().unwrap_or_default();
        let hash_trimmed = hash.trim();

        let date = self.commit_date.clone().unwrap_or_default();
        let date_trimmed = date.trim();

        if (hash_trimmed.len() + date_trimmed.len()) > 0 {
            write!(
                f,
                "{} {}.{}.{} ({hash_trimmed} {date_trimmed})",
                self.crate_name, self.major, self.minor, self.patch,
            )?;
        } else {
            write!(f, "{} {}.{}.{}", self.crate_name, self.major, self.minor, self.patch)?;
        }

        Ok(())
    }
}

impl std::fmt::Debug for VersionInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "VersionInfo {{ crate_name: \"{}\", major: {}, minor: {}, patch: {}",
            self.crate_name, self.major, self.minor, self.patch,
        )?;
        if let Some(ref commit_hash) = self.commit_hash {
            write!(f, ", commit_hash: \"{}\"", commit_hash.trim())?;
        }
        if let Some(ref commit_date) = self.commit_date {
            write!(f, ", commit_date: \"{}\"", commit_date.trim())?;
        }
        if let Some(ref host_compiler) = self.host_compiler {
            write!(f, ", host_compiler: \"{}\"", host_compiler.trim())?;
        }

        write!(f, " }}")?;

        Ok(())
    }
}

// Trust: the command is an `OsStr`, because `RUSTC` is a path.
#[must_use]
fn get_output(cmd: impl AsRef<OsStr>, args: &[&str]) -> Option<String> {
    let output = Command::new(cmd).args(args).output().ok()?;
    let mut stdout = output.status.success().then_some(output.stdout)?;
    // Remove trailing newlines.
    while stdout.last().copied() == Some(b'\n') {
        stdout.pop();
    }
    String::from_utf8(stdout).ok()
}

#[must_use]
pub fn rerun_if_git_changes() -> Option<()> {
    // Make sure we get rerun when the git commit changes.
    // We want to watch two files: HEAD, which tracks which branch we are on,
    // and the file for that branch that tracks which commit is checked out.

    // First, find the `HEAD` file. This should work even with worktrees.
    let git_head_file = PathBuf::from(get_output("git", &["rev-parse", "--git-path", "HEAD"])?);
    if git_head_file.exists() {
        println!("cargo::rerun-if-changed={}", git_head_file.display());
    }

    // Determine the name of the current ref.
    // This will quit if HEAD is detached.
    let git_head_ref = get_output("git", &["symbolic-ref", "-q", "HEAD"])?;
    // Ask git where this ref is stored.
    let git_head_ref_file = PathBuf::from(get_output("git", &["rev-parse", "--git-path", &git_head_ref])?);
    // If this ref is packed, the file does not exist. However, the checked-out branch is never (?)
    // packed, so we should always be able to find this file.
    if git_head_ref_file.exists() {
        println!("cargo::rerun-if-changed={}", git_head_ref_file.display());
    }

    Some(())
}

#[must_use]
pub fn get_commit_hash() -> Option<String> {
    let mut stdout = get_output("git", &["rev-parse", "HEAD"])?;
    stdout.truncate(10);
    Some(stdout)
}

#[must_use]
pub fn get_commit_date() -> Option<String> {
    get_output("git", &["log", "-1", "--date=short", "--pretty=format:%cd"])
}

/// Trust: the commit tuple bootstrap hands a tool's build script: the hash, the short hash and
/// the date of the commit the build is named by (`prepare_tool_cargo`, in bootstrap's
/// `core/build_steps/tool.rs`; targo's `build_commit_info.rs` reads the same three). For a tool
/// built from the Trust checkout's own sources it names what `trustc -vV` names: a dev stage-1
/// build's source identity (`docs/DECISION_QUEUE.md`, TB1-SOURCE-IDENTITY-1), HEAD's commit
/// otherwise.
pub const BOOTSTRAP_COMMIT_ENV: [&str; 3] = ["CFG_COMMIT_HASH", "CFG_SHORT_COMMIT_HASH", "CFG_COMMIT_DATE"];

/// Trust: the hash, cut to 10 digits as [`get_commit_hash`] cuts HEAD's, and the date of the
/// commit that bootstrap's commit tuple ([`BOOTSTRAP_COMMIT_ENV`]) names, or `None` when
/// bootstrap handed no tuple. Cargo is asked to rerun the build script when any of the three
/// changes, set or not, so that the version follows the tuple; when the tuple is set, nothing
/// under `.git` is watched, and a commit that leaves the tuple alone reruns nothing.
///
/// # Panics
///
/// When bootstrap handed the tuple in part, which names no commit.
#[must_use]
pub fn get_bootstrap_commit_info() -> Option<(String, String)> {
    for name in BOOTSTRAP_COMMIT_ENV {
        println!("cargo:rerun-if-env-changed={name}");
    }
    bootstrap_commit_info_of(|name| std::env::var(name).ok())
}

fn bootstrap_commit_info_of(get: impl FnMut(&str) -> Option<String>) -> Option<(String, String)> {
    let values = BOOTSTRAP_COMMIT_ENV.map(get);
    if values.iter().all(Option::is_none) {
        return None;
    }
    let [Some(hash), Some(_), Some(date)] = values else {
        panic!("set all of CFG_COMMIT_HASH, CFG_SHORT_COMMIT_HASH and CFG_COMMIT_DATE, or none");
    };
    Some((hash.chars().take(10).collect(), date))
}

/// The `-V` line of the compiler this build script was handed.
///
/// Trust: cargo hands every build script the compiler it builds with in `RUSTC`, so
/// that is the one asked, at run time. Never a bare `rustc`: a PATH lookup inside a
/// Trust toolchain build is whatever PATH holds, which on most hosts is rustup's
/// stock proxy (measured 2026-10-01: cargo-miri's build script, through the crates.io
/// copy of this crate, ran PATH `rustc -V` in the middle of a seed-rooted stage2
/// build). And never this crate's own compile-time `RUSTC`: a build-dependency is
/// compiled without one unless the caller's environment happens to export it. No
/// `RUSTC`, no answer, and `get_channel` falls back to its default.
#[must_use]
pub fn get_compiler_version() -> Option<String> {
    compiler_version_of(std::env::var_os("RUSTC"))
}

fn compiler_version_of(rustc: Option<OsString>) -> Option<String> {
    let rustc = rustc.filter(|rustc| !rustc.is_empty())?;
    get_output(rustc, &["-V"])
}

#[must_use]
pub fn get_channel(compiler_version: Option<String>) -> String {
    if let Ok(channel) = std::env::var("CFG_RELEASE_CHANNEL") {
        return channel;
    }

    // if that failed, try to ask rustc -V, do some parsing and find out
    if let Some(rustc_output) = compiler_version {
        if rustc_output.contains("beta") {
            return String::from("beta");
        } else if rustc_output.contains("nightly") {
            return String::from("nightly");
        } else if rustc_output.contains("dev") {
            return String::from("dev");
        }
    }

    // default to stable
    String::from("stable")
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_struct_local() {
        let vi = get_version_info!();
        assert_eq!(vi.major, 0);
        assert_eq!(vi.minor, 4);
        assert_eq!(vi.patch, 2);
        assert_eq!(vi.crate_name, "rustc_tools_util");
        // hard to make positive tests for these since they will always change
        assert!(vi.commit_hash.is_none());
        assert!(vi.commit_date.is_none());

        assert!(vi.host_compiler.is_none());
    }

    #[test]
    fn test_display_local() {
        let vi = get_version_info!();
        assert_eq!(vi.to_string(), "rustc_tools_util 0.4.2");
    }

    #[test]
    fn test_debug_local() {
        let vi = get_version_info!();
        let s = format!("{vi:?}");
        assert_eq!(
            s,
            "VersionInfo { crate_name: \"rustc_tools_util\", major: 0, minor: 4, patch: 2 }"
        );
    }

    /// The variables of a commit tuple, `values` in [`BOOTSTRAP_COMMIT_ENV`]'s order.
    fn handed(values: [Option<&'static str>; 3]) -> impl FnMut(&str) -> Option<String> {
        move |name| {
            let at = BOOTSTRAP_COMMIT_ENV.iter().position(|known| *known == name).unwrap();
            values[at].map(str::to_string)
        }
    }

    // Trust: bootstrap's commit tuple names the commit, cut as HEAD's is, when it is handed
    // whole, and nothing when bootstrap handed none.
    #[test]
    fn a_bootstrap_commit_tuple_names_the_commit() {
        let hash = "0123456789abcdef0123456789abcdef01234567";
        assert_eq!(
            bootstrap_commit_info_of(handed([Some(hash), Some("012345678"), Some("2026-10-17")])),
            Some(("0123456789".to_string(), "2026-10-17".to_string()))
        );
        assert_eq!(bootstrap_commit_info_of(handed([None, None, None])), None);
    }

    // Trust: a tuple handed in part names no commit, and neither git's HEAD nor a guess stands in.
    #[test]
    #[should_panic(expected = "or none")]
    fn a_bootstrap_commit_tuple_handed_in_part_is_refused() {
        let _ = bootstrap_commit_info_of(handed([Some("0123456789abcdef"), None, Some("2026-10-17")]));
    }

    // Trust: the compiler-version probe asks the `RUSTC` cargo hands a build script, and
    // never PATH. The probe runs in a child (this test binary, re-executed) whose PATH and
    // RUSTC are exactly what the test sets, whatever environment compiled or runs the suite.
    const PROBE_CHILD: &str = "RUSTC_TOOLS_UTIL_PROBE_CHILD";

    #[test]
    fn compiler_version_probe_child() {
        if std::env::var_os(PROBE_CHILD).is_some() {
            println!("PROBE={:?}", get_compiler_version());
        }
    }

    #[cfg(unix)]
    #[test]
    fn compiler_version_asks_cargos_rustc_never_path() {
        use std::os::unix::fs::PermissionsExt;
        use std::path::Path;
        use std::time::{SystemTime, UNIX_EPOCH};

        let nanos = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let dir = std::env::temp_dir().join(format!("rustc_tools_util-probe-{}-{nanos}", std::process::id()));
        let path_dir = dir.join("path");
        let cargo_dir = dir.join("cargo");
        std::fs::create_dir_all(&path_dir).unwrap();
        std::fs::create_dir_all(&cargo_dir).unwrap();
        let marker = dir.join("path-rustc-ran");
        let script = |file: &Path, body: String| {
            std::fs::write(file, format!("#!/bin/sh\n{body}")).unwrap();
            std::fs::set_permissions(file, std::fs::Permissions::from_mode(0o755)).unwrap();
        };
        // What a PATH lookup would find: on a developer host, rustup's stock proxy.
        script(
            &path_dir.join("rustc"),
            format!(
                ": > '{}'\necho 'rustc 1.98.0 (88d9e12ae 2026-08-28)'\n",
                marker.display()
            ),
        );
        // The compiler cargo builds with, as it hands it to every build script.
        let cargo_rustc = cargo_dir.join("trustc");
        script(
            &cargo_rustc,
            "echo 'rustc 1.99.0-dev (cafe00000 2026-10-01) (trustc)'\n".into(),
        );

        let probe = |rustc: Option<&Path>| -> String {
            let mut child = Command::new(std::env::current_exe().unwrap());
            child
                .args(["--exact", "test::compiler_version_probe_child", "--nocapture"])
                .args(["--test-threads=1", "-q"])
                .env(PROBE_CHILD, "1")
                .env("PATH", &path_dir)
                .env_remove("RUSTC");
            if let Some(rustc) = rustc {
                child.env("RUSTC", rustc);
            }
            let out = child.output().unwrap();
            let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
            assert!(out.status.success(), "probe child failed: {stdout}");
            let line = stdout
                .lines()
                .find_map(|line| line.split_once("PROBE=").map(|(_, rest)| rest));
            line.unwrap_or_else(|| panic!("no PROBE= line in {stdout:?}"))
                .to_owned()
        };

        let with_cargo_rustc = probe(Some(&cargo_rustc));
        let without_rustc = probe(None);
        let path_rustc_ran = marker.exists();
        let _ = std::fs::remove_dir_all(&dir);
        assert_eq!(
            with_cargo_rustc,
            "Some(\"rustc 1.99.0-dev (cafe00000 2026-10-01) (trustc)\")"
        );
        assert_eq!(without_rustc, "None");
        assert!(!path_rustc_ran, "the compiler-version probe executed a PATH `rustc`");
    }
}
