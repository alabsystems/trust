//! Commit-label discovery for Targo's build script.
//!
//! Targo is vendored in the Trust monorepo, unlike upstream Cargo's separate
//! Git submodule. Bootstrap's explicit, validated root tuple is therefore the
//! primary input. The enclosing-checkout Git fallback exists only so a direct
//! developer build has useful version diagnostics; it is not source
//! provenance or verification authority.
//!
//! Trust: Trust-authored, no upstream counterpart. Upstream's `build.rs` can
//! ask Git about the cargo submodule and get an answer that means something.
//! Here the enclosing checkout is the whole monorepo, so the same question
//! yields a commit that is not Targo's — hence the split between an authorized
//! bootstrap-supplied label and a clearly-diagnostic fallback, and the
//! bounded/timed subprocess handling that keeps a hostile or hung repository
//! from stalling the build.

#![cfg_attr(test, allow(dead_code))]
// Build scripts run before Cargo's GlobalContext exists; process environment
// access here is the input boundary rather than a bypass of loaded config.
#![allow(clippy::disallowed_methods)]

use std::collections::BTreeSet;
use std::ffi::{OsStr, OsString};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};
use std::{env, fs, thread};

pub const BOOTSTRAP_COMMIT_ENV: [&str; 3] = [
    "CFG_COMMIT_HASH",
    "CFG_SHORT_COMMIT_HASH",
    "CFG_COMMIT_DATE",
];

const MAX_GIT_STDOUT_BYTES: u64 = 512;
const MAX_GIT_PATH_BYTES: u64 = 64 * 1024;
const MAX_RECORDED_INFO_BYTES: u64 = 512;
const MAX_GIT_RUNTIME: Duration = Duration::from_secs(10);
const MAX_SYMBOLIC_REFS: usize = 8;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommitInfo {
    pub hash: String,
    pub short_hash: String,
    pub date: String,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Discovery {
    pub info: Option<CommitInfo>,
    // These are Cargo freshness inputs for a diagnostic label, never a
    // complete source inventory or provenance/verification authority.
    // Only the selected existing origin/layout is watched. A change in origin
    // or Git layout selection, including creation of previously absent marker,
    // commondir, config.worktree or higher-priority record files, requires a
    // clean rebuild if no already-watched input independently causes rerun.
    pub rerun_if_changed: Vec<PathBuf>,
}

pub fn discover(manifest_dir: &Path, omit_git_hash: bool) -> Result<Discovery, String> {
    discover_with_env(manifest_dir, omit_git_hash, |name| env::var_os(name))
}

fn discover_with_env(
    manifest_dir: &Path,
    omit_git_hash: bool,
    get: impl FnMut(&str) -> Option<OsString>,
) -> Result<Discovery, String> {
    if omit_git_hash {
        return Ok(Discovery {
            info: None,
            rerun_if_changed: Vec::new(),
        });
    }
    if let Some(info) = commit_info_from_bootstrap_env(get)? {
        return Ok(Discovery {
            info: Some(info),
            rerun_if_changed: Vec::new(),
        });
    }

    if let Some(root) = trust_checkout_root(manifest_dir) {
        if plain_git_marker(&root.join(".git")) {
            return discover_git(&root);
        }
    }
    // Preserve upstream Cargo's standalone-checkout behavior when this package
    // really does own a repository. In the Trust tree the package has no such
    // marker, so this can never replace the anchored monorepo identity above.
    if plain_git_marker(&manifest_dir.join(".git")) {
        return discover_git(manifest_dir);
    }

    // Source distributions retain a package-local record for compatibility.
    // The root record is also accepted because vendored Targo has the same
    // commit identity as the rest of the Trust source tree.
    // Cargo treats every absent explicit path as perpetually dirty. Watch
    // only the selected existing record; do not replace missing-path watches
    // with a recursive package-root watch containing Cargo's own outputs.
    // Origin-selection changes need an explicit clean rebuild as documented
    // on `Discovery`; precedence is reevaluated whenever discovery runs.
    for path in [
        Some(manifest_dir.join("git-commit-info")),
        trust_root(manifest_dir).map(|p| p.join("git-commit-info")),
    ]
    .into_iter()
    .flatten()
    {
        if path.exists() {
            return discovery(Some(commit_info_from_recorded_file(&path)?), vec![path]);
        }
    }

    discovery(None, Vec::new())
}

fn discovery(info: Option<CommitInfo>, mut inputs: Vec<PathBuf>) -> Result<Discovery, String> {
    inputs.sort();
    inputs.dedup();
    for path in &inputs {
        let path = path
            .to_str()
            .ok_or("commit-label input path is not UTF-8")?;
        if path.contains(['\n', '\r']) {
            return Err("commit-label input path contains a newline".to_string());
        }
    }
    Ok(Discovery {
        info,
        rerun_if_changed: inputs,
    })
}

fn discover_git(root: &Path) -> Result<Discovery, String> {
    // Resolve paths with the same sanitized native Git authority as `log`.
    // In particular a linked worktree's HEAD and shared branch ref do not
    // live below the same directory. Do not recursively watch `.git`: its
    // objects, index, logs and unrelated refs are not label inputs.
    let git_dir = git_path(root, &["rev-parse", "--absolute-git-dir"])?;
    let common_dir = git_path(root, &["rev-parse", "--git-common-dir"])?;
    let mut inputs = Vec::new();
    for path in [
        root.join(".git"),
        git_dir.join("commondir"),
        common_dir.join("config"),
        git_dir.join("config.worktree"),
    ] {
        if path.is_file() {
            inputs.push(path);
        }
    }

    let mut reference = "HEAD".to_string();
    let mut seen = BTreeSet::new();
    for _ in 0..MAX_SYMBOLIC_REFS {
        if !seen.insert(reference.clone()) {
            return Err("cyclic symbolic reference in commit-label inputs".to_string());
        }
        let path = git_path(root, &["rev-parse", "--git-path", &reference])?;
        if path.is_file() {
            inputs.push(path);
        } else if reference != "HEAD" {
            // A packed ref has no loose file. Watch its existing narrow
            // parent for a new loose override and the packed table for
            // updates. Watching the absent loose file itself would make
            // every native build stale even when HEAD did not move.
            let packed = common_dir.join("packed-refs");
            if !packed.is_file() {
                return Err("commit-label reference has no loose or packed file (unsupported reference storage)".to_string());
            }
            inputs.push(packed);
            let namespace = git_path(root, &["rev-parse", "--git-path", "refs"])?;
            let mut parent = path.parent().ok_or("commit-label ref has no parent")?;
            while !parent.is_dir() {
                parent = parent
                    .parent()
                    .ok_or("commit-label ref parent is missing")?;
            }
            if !parent.starts_with(&namespace) {
                return Err("commit-label ref has no existing refs namespace".to_string());
            }
            inputs.push(parent.to_path_buf());
        } else {
            return Err("commit-label HEAD is not a regular file".to_string());
        }
        let next = git_stdout_status(
            root,
            OsStr::new("git"),
            &["symbolic-ref", "--quiet", "--no-recurse", &reference],
            MAX_GIT_RUNTIME,
            true,
            MAX_GIT_PATH_BYTES,
        )?;
        if let Some(next) = next {
            let next = std::str::from_utf8(&next)
                .map_err(|_| "commit-label symbolic reference is not UTF-8")?;
            let next = next.trim_end();
            // Git has already selected the namespace, but never let malformed
            // metadata become an arbitrary path or build-script instruction.
            if !next.starts_with("refs/")
                || next
                    .split('/')
                    .any(|part| part.is_empty() || part == "." || part == "..")
                || next.chars().any(char::is_whitespace)
                || next.contains('\\')
            {
                return Err("invalid symbolic commit-label reference".to_string());
            }
            reference = next.to_string();
            continue;
        }
        return discovery(Some(commit_info_from_git(root)?), inputs);
    }
    Err("commit-label symbolic reference depth exceeded".to_string())
}

fn git_path(root: &Path, args: &[&str]) -> Result<PathBuf, String> {
    let output = git_stdout_status(
        root,
        OsStr::new("git"),
        args,
        MAX_GIT_RUNTIME,
        false,
        MAX_GIT_PATH_BYTES,
    )?
    .expect("path queries do not accept a non-symbolic status");
    let output = std::str::from_utf8(&output).map_err(|_| "Git path is not UTF-8")?;
    let path = output
        .strip_suffix('\n')
        .unwrap_or(output)
        .trim_end_matches('\r');
    if path.is_empty() || path.contains(['\n', '\r']) {
        return Err("Git returned an empty or multiline metadata path".to_string());
    }
    let path = PathBuf::from(path);
    Ok(if path.is_absolute() {
        path
    } else {
        root.join(path)
    })
}

fn commit_info_from_bootstrap_env(
    mut get: impl FnMut(&str) -> Option<OsString>,
) -> Result<Option<CommitInfo>, String> {
    let values = BOOTSTRAP_COMMIT_ENV.map(|name| get(name));
    let present = values.iter().filter(|value| value.is_some()).count();
    if present == 0 {
        return Ok(None);
    }
    if present != values.len() {
        let names = BOOTSTRAP_COMMIT_ENV
            .into_iter()
            .zip(values.iter())
            .filter_map(|(name, value)| value.is_some().then_some(name))
            .collect::<Vec<_>>()
            .join(", ");
        return Err(format!(
            "bootstrap commit metadata must be all-or-none; present fields: {names}"
        ));
    }

    let [hash, short_hash, date] = values.map(|value| {
        value
            .expect("presence count established the complete tuple")
            .into_string()
            .map_err(|_| "bootstrap commit metadata is not valid UTF-8".to_string())
    });
    validate_tuple(hash?, short_hash?, date?, "bootstrap environment").map(Some)
}

fn commit_info_from_git(root: &Path) -> Result<CommitInfo, String> {
    commit_info_from_git_command(root, OsStr::new("git"), MAX_GIT_RUNTIME)
}

fn commit_info_from_git_command(
    root: &Path,
    program: &OsStr,
    timeout: Duration,
) -> Result<CommitInfo, String> {
    let stdout = git_stdout(
        root,
        program,
        &[
            "log",
            "--no-show-signature",
            "-1",
            "--date=short",
            "--format=%H%n%cd",
        ],
        timeout,
    )?;
    let stdout = String::from_utf8(stdout).map_err(|_| "Git output was not UTF-8".to_string())?;
    let mut lines = stdout.lines();
    let hash = lines
        .next()
        .ok_or_else(|| "Git omitted the commit hash".to_string())?;
    let date = lines
        .next()
        .ok_or_else(|| "Git omitted the commit date".to_string())?;
    if lines.next().is_some() {
        return Err("Git returned duplicate or trailing commit metadata".to_string());
    }
    let short_hash = hash.get(..9).unwrap_or_default();
    validate_tuple(
        hash.to_string(),
        short_hash.to_string(),
        date.to_string(),
        "Git",
    )
}

fn git_stdout(
    root: &Path,
    program: &OsStr,
    args: &[&str],
    timeout: Duration,
) -> Result<Vec<u8>, String> {
    git_stdout_status(root, program, args, timeout, false, MAX_GIT_STDOUT_BYTES)
        .map(|output| output.expect("non-symbolic status is not accepted"))
}

fn git_stdout_status(
    root: &Path,
    program: &OsStr,
    args: &[&str],
    timeout: Duration,
    allow_not_symbolic: bool,
    max_stdout_bytes: u64,
) -> Result<Option<Vec<u8>>, String> {
    let mut command = Command::new(program);
    configure_git_environment(&mut command);
    command
        .arg("--no-pager")
        .arg("-C")
        .arg(root)
        .arg("--no-optional-locks")
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null());

    let mut child = command
        .spawn()
        .map_err(|error| format!("could not execute Git for {}: {error}", root.display()))?;
    let stdout = child.stdout.take().expect("piped Git stdout");
    let (sender, receiver) = mpsc::channel();
    thread::spawn(move || {
        let mut stdout = stdout;
        let mut retained = Vec::new();
        let mut buffer = [0_u8; 1024];
        let mut overflow_reported = false;
        loop {
            match stdout.read(&mut buffer) {
                Ok(0) => {
                    if !overflow_reported {
                        let _ = sender.send(GitReaderEvent::Complete(Ok(retained)));
                    }
                    return;
                }
                Ok(read) => {
                    let remaining = max_stdout_bytes as usize - retained.len();
                    retained.extend_from_slice(&buffer[..read.min(remaining)]);
                    if read > remaining && !overflow_reported {
                        overflow_reported = true;
                        let _ = sender.send(GitReaderEvent::Overflow);
                    }
                }
                Err(error) => {
                    if !overflow_reported {
                        let _ = sender.send(GitReaderEvent::Complete(Err(error.to_string())));
                    }
                    return;
                }
            }
        }
    });

    let deadline = Instant::now() + timeout;
    let mut status = None;
    let mut stdout = None;
    while status.is_none() || stdout.is_none() {
        match receiver.try_recv() {
            Ok(GitReaderEvent::Overflow) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!("Git output exceeded {max_stdout_bytes} bytes"));
            }
            Ok(GitReaderEvent::Complete(Ok(output))) => stdout = Some(output),
            Ok(GitReaderEvent::Complete(Err(error))) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!("could not read Git output: {error}"));
            }
            Err(mpsc::TryRecvError::Empty) => {}
            Err(mpsc::TryRecvError::Disconnected) if stdout.is_none() => {
                let _ = child.kill();
                let _ = child.wait();
                return Err("Git output reader terminated unexpectedly".to_string());
            }
            Err(mpsc::TryRecvError::Disconnected) => {}
        }
        if status.is_none() {
            status = match child.try_wait() {
                Ok(status) => status,
                Err(error) => {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(format!("could not wait for Git: {error}"));
                }
            };
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            return Err(format!(
                "Git exceeded its {} ms diagnostic timeout",
                timeout.as_millis()
            ));
        }
        if status.is_none() || stdout.is_none() {
            thread::sleep(Duration::from_millis(5));
        }
    }

    let status = status.expect("loop requires child status");
    if allow_not_symbolic && status.code() == Some(1) {
        if !stdout.expect("loop requires bounded stdout").is_empty() {
            return Err("Git emitted output for a non-symbolic reference".to_string());
        }
        return Ok(None);
    }
    if !status.success() {
        return Err(format!(
            "Git failed for {} with status {status}",
            root.display()
        ));
    }

    Ok(Some(stdout.expect("loop requires bounded stdout")))
}

enum GitReaderEvent {
    Complete(Result<Vec<u8>, String>),
    Overflow,
}

fn configure_git_environment(command: &mut Command) {
    let inherited_path = env::var_os("PATH");
    let platform = ["SYSTEMROOT", "WINDIR", "COMSPEC", "PATHEXT", "TEMP", "TMP"]
        .map(|name| (name, env::var_os(name)));

    command.env_clear();
    if let Some(path) = inherited_path {
        command.env("PATH", path);
    }
    for (name, value) in platform {
        if let Some(value) = value {
            command.env(name, value);
        }
    }
    command
        .env("LC_ALL", "C")
        .env("LANG", "C")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", null_device())
        .env("GIT_CONFIG_COUNT", "0")
        .env("GIT_TERMINAL_PROMPT", "0")
        .env("GIT_OPTIONAL_LOCKS", "0")
        .env("GIT_NO_REPLACE_OBJECTS", "1")
        // Diagnostic metadata must refuse missing objects, never repair a
        // partial clone. Deny transports even on Git versions that do not
        // recognize lazy-fetch suppression.
        .env("GIT_NO_LAZY_FETCH", "1")
        .env("GIT_ALLOW_PROTOCOL", "");
}

fn null_device() -> &'static OsStr {
    if cfg!(windows) {
        OsStr::new("NUL")
    } else {
        OsStr::new("/dev/null")
    }
}

fn commit_info_from_recorded_file(path: &Path) -> Result<CommitInfo, String> {
    let path_metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("could not inspect {}: {error}", path.display()))?;
    if !path_metadata.file_type().is_file() {
        return Err(format!(
            "{} must be a non-symlink regular file",
            path.display()
        ));
    }
    let file = fs::File::open(path)
        .map_err(|error| format!("could not open {}: {error}", path.display()))?;
    let metadata = file
        .metadata()
        .map_err(|error| format!("could not inspect opened {}: {error}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.len() > MAX_RECORDED_INFO_BYTES {
        return Err(format!(
            "{} must be a regular file no larger than {MAX_RECORDED_INFO_BYTES} bytes",
            path.display()
        ));
    }
    let mut content = Vec::new();
    file.take(MAX_RECORDED_INFO_BYTES + 1)
        .read_to_end(&mut content)
        .map_err(|error| format!("could not read {}: {error}", path.display()))?;
    if content.len() as u64 > MAX_RECORDED_INFO_BYTES {
        return Err(format!(
            "{} grew beyond {MAX_RECORDED_INFO_BYTES} bytes while it was read",
            path.display()
        ));
    }
    let content =
        String::from_utf8(content).map_err(|_| format!("{} is not valid UTF-8", path.display()))?;
    let mut lines = content.lines();
    let hash = lines
        .next()
        .ok_or_else(|| format!("{} omitted the hash", path.display()))?;
    let short_hash = lines
        .next()
        .ok_or_else(|| format!("{} omitted the short hash", path.display()))?;
    let date = lines
        .next()
        .ok_or_else(|| format!("{} omitted the date", path.display()))?;
    if lines.next().is_some() {
        return Err(format!(
            "{} contains trailing commit metadata",
            path.display()
        ));
    }
    validate_tuple(
        hash.to_string(),
        short_hash.to_string(),
        date.to_string(),
        &path.display().to_string(),
    )
}

fn validate_tuple(
    hash: String,
    short_hash: String,
    date: String,
    source: &str,
) -> Result<CommitInfo, String> {
    if !matches!(hash.len(), 40 | 64) || !hash.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(format!(
            "{source} supplied a commit hash that is not a canonical 40- or 64-digit hexadecimal object id"
        ));
    }
    if short_hash.len() != 9 || !short_hash.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(format!(
            "{source} supplied a short hash that is not 9 hexadecimal digits"
        ));
    }
    if !hash[..9].eq_ignore_ascii_case(&short_hash) {
        return Err(format!(
            "{source} supplied a short hash that is not the full hash prefix"
        ));
    }
    if !valid_iso_date(&date) {
        return Err(format!(
            "{source} supplied an invalid YYYY-MM-DD commit date"
        ));
    }
    Ok(CommitInfo {
        hash: hash.to_ascii_lowercase(),
        short_hash: short_hash.to_ascii_lowercase(),
        date,
    })
}

fn valid_iso_date(date: &str) -> bool {
    let bytes = date.as_bytes();
    if bytes.len() != 10
        || bytes[4] != b'-'
        || bytes[7] != b'-'
        || bytes
            .iter()
            .enumerate()
            .any(|(index, byte)| index != 4 && index != 7 && !byte.is_ascii_digit())
    {
        return false;
    }
    let Ok(year) = date[..4].parse::<u32>() else {
        return false;
    };
    let Ok(month) = date[5..7].parse::<u32>() else {
        return false;
    };
    let Ok(day) = date[8..].parse::<u32>() else {
        return false;
    };
    if year == 0 {
        return false;
    }
    let leap = year.is_multiple_of(4) && (!year.is_multiple_of(100) || year.is_multiple_of(400));
    let days = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if leap => 29,
        2 => 28,
        _ => return false,
    };
    (1..=days).contains(&day)
}

fn trust_checkout_root(manifest_dir: &Path) -> Option<PathBuf> {
    let root = trust_root(manifest_dir)?;
    let expected_manifest = root.join("src/tools/targo/Cargo.toml");
    if manifest_dir.join("Cargo.toml") != expected_manifest
        || !root.join("x.py").is_file()
        || !root.join("src/ci/channel").is_file()
        || !root.join("compiler/rustc").is_dir()
        || !root.join("targo-trust/Cargo.toml").is_file()
    {
        return None;
    }
    Some(root)
}

fn plain_git_marker(path: &Path) -> bool {
    fs::symlink_metadata(path).is_ok_and(|metadata| {
        let kind = metadata.file_type();
        kind.is_dir() || kind.is_file()
    })
}

fn trust_root(manifest_dir: &Path) -> Option<PathBuf> {
    if manifest_dir.file_name()? != "targo" || manifest_dir.parent()?.file_name()? != "tools" {
        return None;
    }
    let src = manifest_dir.parent()?.parent()?;
    if src.file_name()? != "src" {
        return None;
    }
    Some(src.parent()?.to_path_buf())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;

    // Trust: preserve the independent local watch regressions at the unified discovery API.
    fn rerun_paths_with_env(
        root: &Path,
        omit: bool,
        get: impl FnMut(&str) -> Option<OsString>,
    ) -> Result<Vec<PathBuf>, String> {
        discover_with_env(root, omit, get).map(|result| result.rerun_if_changed)
    }

    fn watch_git_path(root: &Path, name: &OsStr) -> Result<PathBuf, String> {
        git_path(root, &["rev-parse", "--git-path", name.to_str().ok_or("non-UTF-8 test ref")?])
    }

    fn watch_fixture() -> PathBuf {
        // Timestamp-derived names can collide between concurrently starting
        // tests on clocks with coarser resolution than SystemTime's type.
        let root = tempfile::Builder::new()
            .prefix("targo-version-watch-")
            .tempdir()
            .unwrap()
            .keep();
        watch_git(&root, &["init", "-q"]);
        watch_git(&root, &["symbolic-ref", "HEAD", "refs/heads/version-watch"]);
        fs::write(root.join("Cargo.toml"), "fixture\n").unwrap();
        watch_git(&root, &["add", "Cargo.toml"]);
        watch_git(
            &root,
            &["commit", "-q", "-m", "initial version watch fixture"],
        );
        root
    }

    fn watch_git(root: &Path, args: &[&str]) {
        let mut command = Command::new("git");
        configure_git_environment(&mut command);
        let output = command
            .arg("-C")
            .arg(root)
            .args([
                "-c",
                "user.name=Version fixture",
                "-c",
                "user.email=fixture@example.invalid",
                "-c",
                "commit.gpgsign=false",
            ])
            .args(args)
            .output()
            .unwrap();
        assert!(output.status.success(), "Git {args:?}: {:?}", output.stderr);
    }

    #[test]
    fn watches_loose_branch_when_commits_leave_head_file_unchanged() {
        let root = watch_fixture();
        let head = watch_git_path(&root, OsStr::new("HEAD")).unwrap();
        let branch = watch_git_path(&root, OsStr::new("refs/heads/version-watch")).unwrap();
        let before_head = fs::read(&head).unwrap();
        let before_ref = fs::read(&branch).unwrap();
        let paths = rerun_paths_with_env(&root, false, |_| None).unwrap();
        assert!(paths.contains(&head) && paths.contains(&branch));
        watch_git(
            &root,
            &[
                "commit",
                "-q",
                "--allow-empty",
                "-m",
                "advance metadata only",
            ],
        );
        assert_eq!(fs::read(&head).unwrap(), before_head);
        assert_ne!(fs::read(&branch).unwrap(), before_ref);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn packed_reference_watch_uses_existing_inputs_and_detects_loose_creation() {
        let root = watch_fixture();
        watch_git(&root, &["pack-refs", "--all", "--prune"]);
        let branch = watch_git_path(&root, OsStr::new("refs/heads/version-watch")).unwrap();
        assert!(!branch.exists());
        let paths = rerun_paths_with_env(&root, false, |_| None).unwrap();
        assert!(paths.iter().all(|path| path.exists()));
        assert!(paths.contains(&watch_git_path(&root, OsStr::new("packed-refs")).unwrap()));
        assert!(paths.contains(&branch.parent().unwrap().to_path_buf()));
        watch_git(
            &root,
            &[
                "commit",
                "-q",
                "--allow-empty",
                "-m",
                "recreate loose reference",
            ],
        );
        assert!(branch.is_file());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn linked_worktree_watches_its_head_marker_common_pointer_and_shared_ref() {
        let root = watch_fixture();
        let linked = root.join("linked");
        watch_git(
            &root,
            &[
                "worktree",
                "add",
                "-q",
                "-b",
                "linked-version-watch",
                linked.to_str().unwrap(),
            ],
        );
        let paths = rerun_paths_with_env(&linked, false, |_| None).unwrap();
        let head = watch_git_path(&linked, OsStr::new("HEAD")).unwrap();
        let branch = watch_git_path(&linked, OsStr::new("refs/heads/linked-version-watch")).unwrap();
        assert!(paths.contains(&linked.join(".git")));
        assert!(paths.contains(&head));
        assert!(paths.contains(&head.parent().unwrap().join("commondir")));
        assert!(paths.contains(&branch));
        assert_ne!(head.parent(), branch.parent());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn detached_head_is_watched_without_unrelated_branch_dependencies() {
        let root = watch_fixture();
        watch_git(&root, &["checkout", "-q", "--detach"]);
        let paths = rerun_paths_with_env(&root, false, |_| None).unwrap();
        let mut expected = vec![watch_git_path(&root, OsStr::new("HEAD")).unwrap(), root.join(".git/config")];
        expected.sort();
        assert_eq!(paths, expected, "only HEAD and Git configuration affect a detached label");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn anchored_monorepo_watches_root_git_without_package_git_marker() {
        let root = watch_fixture();
        let manifest = root.join("src/tools/targo");
        for directory in [
            &manifest,
            &root.join("src/ci"),
            &root.join("compiler/rustc"),
            &root.join("targo-trust"),
        ] {
            fs::create_dir_all(directory).unwrap();
        }
        for file in [
            manifest.join("Cargo.toml"),
            root.join("src/ci/channel"),
            root.join("x.py"),
            root.join("targo-trust/Cargo.toml"),
        ] {
            fs::write(file, "fixture\n").unwrap();
        }
        let paths = rerun_paths_with_env(&manifest, false, |_| None).unwrap();
        assert!(!manifest.join(".git").exists());
        assert!(paths.contains(&watch_git_path(&root, OsStr::new("HEAD")).unwrap()));
        assert!(paths.contains(&watch_git_path(&root, OsStr::new("refs/heads/version-watch")).unwrap()));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn intermediate_symbolic_reference_is_an_input_too() {
        let root = watch_fixture();
        watch_git(&root, &["branch", "label-target"]);
        watch_git(
            &root,
            &[
                "symbolic-ref",
                "refs/heads/version-watch",
                "refs/heads/label-target",
            ],
        );
        let paths = rerun_paths_with_env(&root, false, |_| None).unwrap();
        for reference in [
            "HEAD",
            "refs/heads/version-watch",
            "refs/heads/label-target",
        ] {
            assert!(paths.contains(&watch_git_path(&root, OsStr::new(reference)).unwrap()));
        }
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn explicit_and_omitted_labels_do_not_query_git_or_add_checkout_watches() {
        let root = watch_fixture();
        fs::remove_dir_all(root.join(".git")).unwrap();
        fs::write(
            root.join(".git"),
            "invalid Git marker to detect accidental fallback\n",
        )
        .unwrap();
        let hash = "0123456789abcdef0123456789abcdef01234567";
        let values = BTreeMap::from([
            ("CFG_COMMIT_HASH", OsString::from(hash)),
            ("CFG_SHORT_COMMIT_HASH", OsString::from("012345678")),
            ("CFG_COMMIT_DATE", OsString::from("2026-10-22")),
        ]);
        assert!(
            rerun_paths_with_env(&root, false, |name| values.get(name).cloned())
                .unwrap()
                .is_empty()
        );
        assert!(
            rerun_paths_with_env(&root, true, |_| Some(OsString::from("invalid")))
                .unwrap()
                .is_empty()
        );
        assert!(
            rerun_paths_with_env(&root, false, |name| (name == "CFG_COMMIT_HASH")
                .then(|| OsString::from(hash)))
            .unwrap_err()
            .contains("all-or-none")
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn source_record_is_watched_but_unbound_package_needs_no_git() {
        let root = env::temp_dir().join(format!(
            "targo-unbound-version-watch-{}",
            std::process::id()
        ));
        fs::create_dir_all(&root).unwrap();
        assert!(
            rerun_paths_with_env(&root, false, |_| None)
                .unwrap()
                .is_empty()
        );
        let record = root.join("git-commit-info");
        fs::write(
            &record,
            "0123456789abcdef0123456789abcdef01234567\n012345678\n2026-10-22\n",
        )
        .unwrap();
        assert_eq!(
            rerun_paths_with_env(&root, false, |_| None).unwrap(),
            [record]
        );
        fs::remove_dir_all(root).unwrap();
    }

    fn native_git(root: &Path, args: &[&str]) -> String {
        let mut command = Command::new("git");
        configure_git_environment(&mut command);
        let output = command
            .arg("-C")
            .arg(root)
            .args([
                "-c",
                "user.name=Commit Label Test",
                "-c",
                "user.email=commit-label@example.invalid",
            ])
            .args(args)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "fixture Git {args:?} failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap().trim().to_string()
    }

    fn native_fixture() -> tempfile::TempDir {
        let root = tempfile::tempdir().unwrap();
        native_git(root.path(), &["init", "--quiet"]);
        native_git(root.path(), &["symbolic-ref", "HEAD", "refs/heads/main"]);
        fs::write(root.path().join("Cargo.toml"), "fixture\n").unwrap();
        native_git(root.path(), &["add", "Cargo.toml"]);
        native_git(
            root.path(),
            &["commit", "--quiet", "--no-gpg-sign", "-m", "first"],
        );
        root
    }

    #[test]
    fn native_loose_and_detached_labels_watch_the_selected_inputs() {
        let fixture = native_fixture();
        let root = fixture.path();
        let before = discover_with_env(root, false, |_| None).unwrap();
        let head = git_path(root, &["rev-parse", "--git-path", "HEAD"]).unwrap();
        let branch = git_path(root, &["rev-parse", "--git-path", "refs/heads/main"]).unwrap();
        assert!(before.rerun_if_changed.contains(&head));
        assert!(before.rerun_if_changed.contains(&branch));
        assert!(
            before.rerun_if_changed.iter().all(|path| path.is_file()),
            "a loose native ref needs no recursive directory watch"
        );
        let head_bytes = fs::read(&head).unwrap();
        let branch_bytes = fs::read(&branch).unwrap();
        native_git(
            root,
            &[
                "commit",
                "--quiet",
                "--allow-empty",
                "--no-gpg-sign",
                "-m",
                "second",
            ],
        );
        let advanced = discover_with_env(root, false, |_| None).unwrap();
        assert_ne!(before.info, advanced.info);
        assert_eq!(before.rerun_if_changed, advanced.rerun_if_changed);
        assert_eq!(
            fs::read(&head).unwrap(),
            head_bytes,
            "HEAD alone cannot detect a branch advance"
        );
        assert_ne!(fs::read(&branch).unwrap(), branch_bytes);

        native_git(root, &["checkout", "--quiet", "--detach", "HEAD"]);
        let detached = discover_with_env(root, false, |_| None).unwrap();
        assert_eq!(advanced.info, detached.info);
        assert!(detached.rerun_if_changed.contains(&head));
        assert!(!detached.rerun_if_changed.contains(&branch));
        assert_ne!(fs::read(&head).unwrap(), head_bytes);
        native_git(root, &["checkout", "--quiet", "--detach", "HEAD^"]);
        assert_eq!(
            discover_with_env(root, false, |_| None).unwrap().info,
            before.info
        );
    }

    #[test]
    fn native_packed_label_watches_packed_table_and_new_loose_override() {
        let fixture = native_fixture();
        let root = fixture.path();
        native_git(root, &["branch", "-m", "topic/main"]);
        let first = native_git(root, &["rev-parse", "HEAD"]);
        native_git(
            root,
            &[
                "commit",
                "--quiet",
                "--allow-empty",
                "--no-gpg-sign",
                "-m",
                "second",
            ],
        );
        let second = native_git(root, &["rev-parse", "HEAD"]);
        native_git(root, &["update-ref", "refs/heads/topic/main", &first]);
        let loose = discover_with_env(root, false, |_| None).unwrap();
        let branch = git_path(root, &["rev-parse", "--git-path", "refs/heads/topic/main"]).unwrap();
        assert!(loose.rerun_if_changed.contains(&branch));
        native_git(root, &["pack-refs", "--all", "--prune"]);
        assert!(
            !branch.exists(),
            "native pack-refs must exercise the absent-loose path"
        );
        if branch.parent().unwrap().exists() {
            fs::remove_dir(branch.parent().unwrap()).unwrap();
        }
        let packed = discover_with_env(root, false, |_| None).unwrap();
        let table = git_path(root, &["rev-parse", "--git-path", "packed-refs"]).unwrap();
        let parent = git_path(root, &["rev-parse", "--git-path", "refs/heads"]).unwrap();
        assert_eq!(loose.info, packed.info);
        assert!(packed.rerun_if_changed.contains(&table));
        assert!(packed.rerun_if_changed.contains(&parent));
        assert!(
            packed.rerun_if_changed.iter().all(|path| path.exists()),
            "missing native watches would perpetually rebuild"
        );
        assert!(
            !packed.rerun_if_changed.contains(&root.join(".git")),
            "never recursively watch the whole Git directory"
        );
        let table_bytes = fs::read(&table).unwrap();
        assert!(
            !fs::read_dir(&parent)
                .unwrap()
                .any(|entry| entry.unwrap().file_name() == "topic")
        );

        native_git(root, &["update-ref", "refs/heads/topic/main", &second]);
        assert_eq!(
            fs::read(&table).unwrap(),
            table_bytes,
            "a loose override does not update packed-refs"
        );
        assert!(
            fs::read_dir(&parent)
                .unwrap()
                .any(|entry| entry.unwrap().file_name() == "topic")
        );
        let overridden = discover_with_env(root, false, |_| None).unwrap();
        assert_ne!(packed.info, overridden.info);
        assert_eq!(overridden.info.unwrap().hash, second);
        assert!(overridden.rerun_if_changed.contains(&branch));
        assert!(!overridden.rerun_if_changed.contains(&parent));
        native_git(root, &["pack-refs", "--all", "--prune"]);
        let repacked = discover_with_env(root, false, |_| None).unwrap();
        assert_eq!(repacked.info.unwrap().hash, second);
        assert!(repacked.rerun_if_changed.contains(&table));
        assert_ne!(fs::read(&table).unwrap(), table_bytes);
    }

    #[test]
    fn native_linked_worktree_binds_private_head_and_common_branch() {
        let fixture = native_fixture();
        let root = fixture.path();
        native_git(
            root,
            &[
                "commit",
                "--quiet",
                "--allow-empty",
                "--no-gpg-sign",
                "-m",
                "second",
            ],
        );
        let second = native_git(root, &["rev-parse", "HEAD"]);
        let linked = root.join("linked-worktree");
        native_git(
            root,
            &[
                "worktree",
                "add",
                "--quiet",
                "-b",
                "linked",
                linked.to_str().unwrap(),
                "HEAD^",
            ],
        );
        let private = git_path(&linked, &["rev-parse", "--absolute-git-dir"]).unwrap();
        let common = git_path(&linked, &["rev-parse", "--git-common-dir"]).unwrap();
        assert_ne!(private, common);
        native_git(root, &["config", "extensions.worktreeConfig", "true"]);
        let worktree_config = private.join("config.worktree");
        assert!(!worktree_config.exists());
        let common_config = fs::read(common.join("config")).unwrap();
        let head = git_path(&linked, &["rev-parse", "--git-path", "HEAD"]).unwrap();
        let branch = git_path(&linked, &["rev-parse", "--git-path", "refs/heads/linked"]).unwrap();
        let before = discover_with_env(&linked, false, |_| None).unwrap();
        for path in [
            linked.join(".git"),
            private.join("commondir"),
            common.join("config"),
            head.clone(),
            branch.clone(),
        ] {
            assert!(
                before.rerun_if_changed.contains(&path),
                "missing {}",
                path.display()
            );
        }
        assert!(!before.rerun_if_changed.contains(&private));
        assert!(!before.rerun_if_changed.contains(&common));
        assert!(!before.rerun_if_changed.contains(&worktree_config));
        let head_bytes = fs::read(&head).unwrap();
        native_git(root, &["update-ref", "refs/heads/linked", &second]);
        let after = discover_with_env(&linked, false, |_| None).unwrap();
        assert_ne!(before.info, after.info);
        assert_eq!(after.info.unwrap().hash, second);
        assert_eq!(fs::read(&head).unwrap(), head_bytes);
        assert_eq!(before.rerun_if_changed, after.rerun_if_changed);

        // Creation alone is outside automatic freshness coverage: enabling
        // the extension happened before the original discovery above.
        native_git(&linked, &["config", "--worktree", "test.label", "changed"]);
        assert_eq!(fs::read(common.join("config")).unwrap(), common_config);
        assert!(
            discover_with_env(&linked, false, |_| None)
                .unwrap()
                .rerun_if_changed
                .contains(&worktree_config)
        );
        fs::write(&worktree_config, "[malformed\n").unwrap();
        let error = discover_with_env(&linked, false, |_| None).unwrap_err();
        assert!(error.contains("Git failed"), "{error}");
    }

    #[test]
    fn native_symbolic_chain_watches_each_ref_and_refuses_cycles() {
        let fixture = native_fixture();
        let root = fixture.path();
        let original = discover_with_env(root, false, |_| None).unwrap();
        native_git(
            root,
            &["symbolic-ref", "refs/heads/alias", "refs/heads/main"],
        );
        native_git(root, &["symbolic-ref", "HEAD", "refs/heads/alias"]);
        let chained = discover_with_env(root, false, |_| None).unwrap();
        assert_eq!(chained.info, original.info);
        let alias = git_path(root, &["rev-parse", "--git-path", "refs/heads/alias"]).unwrap();
        assert!(chained.rerun_if_changed.contains(&alias));
        assert!(
            original
                .rerun_if_changed
                .iter()
                .all(|path| chained.rerun_if_changed.contains(path))
        );
        fs::write(alias, "ref: refs/heads/alias\n").unwrap();
        let error = discover_with_env(root, false, |_| None).unwrap_err();
        assert!(error.contains("cyclic symbolic reference"), "{error}");

        for depth in 0..MAX_SYMBOLIC_REFS {
            let current = format!("refs/heads/depth{depth}");
            let next = format!("refs/heads/depth{}", depth + 1);
            let path = git_path(root, &["rev-parse", "--git-path", &current]).unwrap();
            fs::write(path, format!("ref: {next}\n")).unwrap();
        }
        let head = git_path(root, &["rev-parse", "--git-path", "HEAD"]).unwrap();
        fs::write(head, "ref: refs/heads/depth0\n").unwrap();
        let error = discover_with_env(root, false, |_| None).unwrap_err();
        assert!(
            error.contains("symbolic reference depth exceeded"),
            "{error}"
        );
        assert!(discovery(None, vec![root.join("bad\ncargo:rustc-env=forged")]).is_err());
    }

    #[test]
    fn recorded_label_inputs_preserve_precedence_creation_and_refusal() {
        let fixture = tempfile::tempdir().unwrap();
        let root = fixture.path();
        let manifest = root.join("src/tools/targo");
        fs::create_dir_all(&manifest).unwrap();
        let record = root.join("git-commit-info");
        let local = manifest.join("git-commit-info");
        let first = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\naaaaaaaaa\n2026-10-24\n";
        let second = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\nbbbbbbbbb\n2026-10-24\n";
        let absent = discover_with_env(&manifest, false, |_| None).unwrap();
        assert_eq!(absent.info, None);
        assert!(absent.rerun_if_changed.is_empty());
        fs::write(&record, first).unwrap();
        let root_record = discover_with_env(&manifest, false, |_| None).unwrap();
        assert_eq!(root_record.info.as_ref().unwrap().short_hash, "aaaaaaaaa");
        assert_eq!(root_record.rerun_if_changed, vec![record.clone()]);
        fs::write(&local, second).unwrap();
        let local_record = discover_with_env(&manifest, false, |_| None).unwrap();
        assert_eq!(local_record.info.unwrap().short_hash, "bbbbbbbbb");
        assert!(local_record.rerun_if_changed.contains(&local));
        assert!(!local_record.rerun_if_changed.contains(&record));
        fs::write(&local, "malformed\n").unwrap();
        assert!(
            discover_with_env(&manifest, false, |_| None).is_err(),
            "a bad selected local record must not fall back to the valid root record"
        );
        fs::remove_file(&local).unwrap();
        assert_eq!(
            discover_with_env(&manifest, false, |_| None).unwrap().info,
            root_record.info
        );
        fs::write(&record, second).unwrap();
        assert_ne!(
            discover_with_env(&manifest, false, |_| None).unwrap().info,
            root_record.info
        );

        // On an explicit rediscovery (for example after clean), a complete
        // Trust checkout replaces the still-valid recorded archive label.
        for dir in [
            root.join("compiler/rustc"),
            root.join("src/ci"),
            root.join("targo-trust"),
        ] {
            fs::create_dir_all(dir).unwrap();
        }
        for file in [
            root.join("x.py"),
            root.join("src/ci/channel"),
            root.join("targo-trust/Cargo.toml"),
            manifest.join("Cargo.toml"),
        ] {
            fs::write(file, "fixture\n").unwrap();
        }
        native_git(root, &["init", "--quiet"]);
        native_git(root, &["add", "x.py"]);
        native_git(
            root,
            &["commit", "--quiet", "--no-gpg-sign", "-m", "checkout"],
        );
        let checkout = discover_with_env(&manifest, false, |_| None).unwrap();
        assert_eq!(
            checkout.info.unwrap().hash,
            native_git(root, &["rev-parse", "HEAD"])
        );
        assert!(!checkout.rerun_if_changed.contains(&record));
        assert!(!checkout.rerun_if_changed.contains(&root.join(".git")));
    }

    fn env_tuple(values: &[(&str, &str)]) -> Result<Option<CommitInfo>, String> {
        let values = values
            .iter()
            .map(|(name, value)| ((*name).to_string(), OsString::from(value)))
            .collect::<BTreeMap<_, _>>();
        commit_info_from_bootstrap_env(|name| values.get(name).cloned())
    }

    #[test]
    fn explicit_bootstrap_tuple_is_all_or_none_and_validated() {
        let hash = "0123456789abcdef0123456789abcdef01234567";
        assert_eq!(env_tuple(&[]).unwrap(), None);
        assert_eq!(
            env_tuple(&[
                ("CFG_COMMIT_HASH", hash),
                ("CFG_SHORT_COMMIT_HASH", "012345678"),
                ("CFG_COMMIT_DATE", "2024-02-29"),
            ])
            .unwrap(),
            Some(CommitInfo {
                hash: hash.to_string(),
                short_hash: "012345678".to_string(),
                date: "2024-02-29".to_string(),
            })
        );
        let sha256 = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
        assert_eq!(
            env_tuple(&[
                ("CFG_COMMIT_HASH", sha256),
                ("CFG_SHORT_COMMIT_HASH", "012345678"),
                ("CFG_COMMIT_DATE", "2024-02-29"),
            ])
            .unwrap()
            .unwrap()
            .hash,
            sha256,
        );
        assert!(
            env_tuple(&[("CFG_COMMIT_HASH", hash)])
                .unwrap_err()
                .contains("all-or-none")
        );
        assert!(
            env_tuple(&[
                ("CFG_COMMIT_HASH", hash),
                ("CFG_SHORT_COMMIT_HASH", "fffffffff"),
                ("CFG_COMMIT_DATE", "2024-02-29"),
            ])
            .unwrap_err()
            .contains("prefix")
        );
        assert!(
            env_tuple(&[
                ("CFG_COMMIT_HASH", "0123456789abcdef0123456789abcdef0123456"),
                ("CFG_SHORT_COMMIT_HASH", "012345678"),
                ("CFG_COMMIT_DATE", "2024-02-29"),
            ])
            .unwrap_err()
            .contains("40- or 64-digit")
        );
        assert!(
            env_tuple(&[
                ("CFG_COMMIT_HASH", hash),
                ("CFG_SHORT_COMMIT_HASH", "01234567"),
                ("CFG_COMMIT_DATE", "2024-02-29"),
            ])
            .unwrap_err()
            .contains("9 hexadecimal")
        );
        assert!(
            env_tuple(&[
                ("CFG_COMMIT_HASH", hash),
                ("CFG_SHORT_COMMIT_HASH", "012345678"),
                ("CFG_COMMIT_DATE", "2023-02-29"),
            ])
            .unwrap_err()
            .contains("YYYY-MM-DD")
        );
    }

    #[test]
    fn vendored_targo_checkout_uses_anchored_root_without_local_git_dir() {
        let root = env::temp_dir().join(format!(
            "targo-build-commit-info-test-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let manifest_dir = root.join("src/tools/targo");
        for dir in [
            &manifest_dir,
            &root.join("src/ci"),
            &root.join("compiler/rustc"),
            &root.join("targo-trust"),
        ] {
            fs::create_dir_all(dir).unwrap();
        }
        for file in [
            manifest_dir.join("Cargo.toml"),
            root.join("src/ci/channel"),
            root.join("targo-trust/Cargo.toml"),
            root.join("x.py"),
            root.join(".git"),
        ] {
            fs::write(file, "test").unwrap();
        }

        assert!(!manifest_dir.join(".git").exists());
        assert_eq!(
            trust_checkout_root(&manifest_dir).as_deref(),
            Some(root.as_path())
        );

        let explicit_hash = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        let explicit = [
            ("CFG_COMMIT_HASH", explicit_hash),
            ("CFG_SHORT_COMMIT_HASH", "aaaaaaaaa"),
            ("CFG_COMMIT_DATE", "2026-07-14"),
        ]
        .into_iter()
        .map(|(name, value)| (name.to_string(), OsString::from(value)))
        .collect::<BTreeMap<_, _>>();
        let supplied =
            discover_with_env(&manifest_dir, false, |name| explicit.get(name).cloned()).unwrap();
        assert!(
            supplied.rerun_if_changed.is_empty(),
            "explicit bootstrap labels must not acquire ambient Git/source dependencies"
        );
        assert_eq!(
            supplied.info,
            Some(CommitInfo {
                hash: explicit_hash.to_string(),
                short_hash: "aaaaaaaaa".to_string(),
                date: "2026-07-14".to_string(),
            }),
            "the explicit bootstrap tuple must preempt checkout diagnostics"
        );
        let partial =
            BTreeMap::from([("CFG_COMMIT_HASH".to_string(), OsString::from(explicit_hash))]);
        assert!(
            discover_with_env(&manifest_dir, false, |name| partial.get(name).cloned())
                .unwrap_err()
                .contains("all-or-none"),
            "a partial explicit tuple must not downgrade to checkout discovery"
        );
        assert_eq!(
            discover_with_env(&manifest_dir, true, |name| partial.get(name).cloned()).unwrap(),
            Discovery {
                info: None,
                rerun_if_changed: Vec::new()
            },
            "CFG_OMIT_GIT_HASH must suppress even malformed ambient metadata and checkout fallback"
        );

        fs::remove_file(root.join("targo-trust/Cargo.toml")).unwrap();
        assert_eq!(trust_checkout_root(&manifest_dir), None);
        fs::remove_dir_all(root).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn diagnostic_git_fallback_never_fetches_promisor_head() {
        use std::os::unix::fs::PermissionsExt;

        let root = env::temp_dir().join(format!(
            "targo-build-commit-promisor-test-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir_all(&root).unwrap();
        struct Cleanup(PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(root.clone());
        let git = |args: &[&str]| {
            let mut command = Command::new("git");
            configure_git_environment(&mut command);
            let output = command.arg("-C").arg(&root).args(args).output().unwrap();
            assert!(
                output.status.success(),
                "fixture Git failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        };
        git(&["init", "--quiet"]);
        let ssh = root.join("fake-ssh");
        let contacted = root.join("fake-ssh.contacted");
        fs::write(
            &ssh,
            "#!/bin/sh\nprintf '%s\\n' contacted > \"$0.contacted\"\nexit 1\n",
        )
        .unwrap();
        fs::set_permissions(&ssh, fs::Permissions::from_mode(0o755)).unwrap();
        let ssh_command = format!("'{}'", ssh.to_str().unwrap().replace('\'', "'\\''"));
        git(&["config", "core.sshCommand", &ssh_command]);
        git(&["config", "ssh.variant", "ssh"]);
        git(&[
            "config",
            "remote.origin.url",
            "ssh://metadata-fixture.invalid/missing",
        ]);
        git(&["config", "remote.origin.promisor", "true"]);
        git(&["config", "remote.origin.partialCloneFilter", "blob:none"]);

        // An unreadable promisor HEAD must refuse locally, never repair the
        // repository or invoke a transport while discovering a diagnostic label.
        let head = b"1111111111111111111111111111111111111111\n";
        fs::write(root.join(".git/HEAD"), b"ref: refs/heads/main\n").unwrap();
        fs::write(root.join(".git/refs/heads/main"), head).unwrap();
        let config = fs::read(root.join(".git/config")).unwrap();

        // Native positive control: this same repository really invokes SSH
        // when lazy fetching and the SSH transport are explicitly permitted.
        // The helper exits locally, so no network is contacted.
        let mut online = Command::new("git");
        configure_git_environment(&mut online);
        let output = online
            .env_remove("GIT_NO_LAZY_FETCH")
            .env("GIT_ALLOW_PROTOCOL", "ssh")
            .arg("-C")
            .arg(&root)
            .args(["log", "-1", "--format=%H%n%cd"])
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(
            contacted.exists(),
            "native Git must exercise the promisor transport"
        );
        fs::remove_file(&contacted).unwrap();

        let error = commit_info_from_git_command(&root, OsStr::new("git"), Duration::from_secs(2))
            .unwrap_err();
        assert!(error.contains("Git failed"), "{error}");
        assert!(
            !contacted.exists(),
            "diagnostic Git must never invoke a transport"
        );
        assert_eq!(fs::read(root.join(".git/config")).unwrap(), config);
        assert_eq!(fs::read(root.join(".git/refs/heads/main")).unwrap(), head);

        // The transport prohibition must also hold when a Git version does
        // not honor lazy-fetch suppression.
        let mut transport_only = Command::new("git");
        configure_git_environment(&mut transport_only);
        let output = transport_only
            .env("GIT_NO_LAZY_FETCH", "0")
            .arg("-C")
            .arg(&root)
            .args(["log", "-1", "--format=%H%n%cd"])
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(
            !contacted.exists(),
            "transport denial must independently hold"
        );
    }

    #[cfg(unix)]
    #[test]
    fn diagnostic_git_fallback_is_time_and_output_bounded() {
        use std::os::unix::fs::PermissionsExt;

        let root = env::temp_dir().join(format!(
            "targo-build-commit-timeout-test-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir_all(&root).unwrap();
        let fake_git = root.join("git");
        fs::write(&fake_git, "#!/bin/sh\nwhile :; do :; done\n").unwrap();
        fs::set_permissions(&fake_git, fs::Permissions::from_mode(0o755)).unwrap();

        let started = Instant::now();
        let error =
            commit_info_from_git_command(&root, fake_git.as_os_str(), Duration::from_millis(50))
                .unwrap_err();
        assert!(error.contains("timeout"), "{error}");
        assert!(started.elapsed() < Duration::from_secs(2));

        fs::write(
            &fake_git,
            "#!/bin/sh\ni=0\nwhile [ \"$i\" -lt 100 ]; do\n  printf '0123456789abcdef0123456789abcdef\\n'\n  i=$((i + 1))\ndone\n",
        )
        .unwrap();
        let started = Instant::now();
        let error =
            commit_info_from_git_command(&root, fake_git.as_os_str(), Duration::from_secs(1))
                .unwrap_err();
        assert!(error.contains("output exceeded"), "{error}");
        assert!(started.elapsed() < Duration::from_secs(2));
        fs::remove_dir_all(root).unwrap();
    }
}
