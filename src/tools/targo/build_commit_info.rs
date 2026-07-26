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

use std::env;
use std::ffi::{OsStr, OsString};
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

pub const BOOTSTRAP_COMMIT_ENV: [&str; 3] = [
    "CFG_COMMIT_HASH",
    "CFG_SHORT_COMMIT_HASH",
    "CFG_COMMIT_DATE",
];

const MAX_GIT_STDOUT_BYTES: u64 = 512;
const MAX_RECORDED_INFO_BYTES: u64 = 512;
const MAX_GIT_RUNTIME: Duration = Duration::from_secs(10);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommitInfo {
    pub hash: String,
    pub short_hash: String,
    pub date: String,
}

pub fn discover(manifest_dir: &Path, omit_git_hash: bool) -> Result<Option<CommitInfo>, String> {
    discover_with_env(manifest_dir, omit_git_hash, |name| env::var_os(name))
}

fn discover_with_env(
    manifest_dir: &Path,
    omit_git_hash: bool,
    get: impl FnMut(&str) -> Option<OsString>,
) -> Result<Option<CommitInfo>, String> {
    if omit_git_hash {
        return Ok(None);
    }
    if let Some(info) = commit_info_from_bootstrap_env(get)? {
        return Ok(Some(info));
    }

    if let Some(root) = trust_checkout_root(manifest_dir) {
        if plain_git_marker(&root.join(".git")) {
            return commit_info_from_git(&root).map(Some);
        }
    }
    // Preserve upstream Cargo's standalone-checkout behavior when this package
    // really does own a repository. In the Trust tree the package has no such
    // marker, so this can never replace the anchored monorepo identity above.
    if plain_git_marker(&manifest_dir.join(".git")) {
        return commit_info_from_git(manifest_dir).map(Some);
    }

    // Source distributions retain a package-local record for compatibility.
    // The root record is also accepted because vendored Targo has the same
    // commit identity as the rest of the Trust source tree.
    for path in [
        Some(manifest_dir.join("git-commit-info")),
        trust_root(manifest_dir).map(|p| p.join("git-commit-info")),
    ]
    .into_iter()
    .flatten()
    {
        if path.exists() {
            return commit_info_from_recorded_file(&path).map(Some);
        }
    }

    Ok(None)
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
    let mut command = Command::new(program);
    configure_git_environment(&mut command);
    command
        .arg("--no-pager")
        .arg("-C")
        .arg(root)
        .arg("--no-optional-locks")
        .arg("log")
        .arg("--no-show-signature")
        .arg("-1")
        .arg("--date=short")
        .arg("--format=%H%n%cd")
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
                    let remaining = MAX_GIT_STDOUT_BYTES as usize - retained.len();
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
                return Err(format!("Git output exceeded {MAX_GIT_STDOUT_BYTES} bytes"));
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
    if !status.success() {
        return Err(format!(
            "Git failed for {} with status {status}",
            root.display()
        ));
    }

    let stdout = stdout.expect("loop requires bounded stdout");
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
        .env("GIT_NO_REPLACE_OBJECTS", "1");
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
    use super::*;
    use std::collections::BTreeMap;

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
        assert_eq!(
            discover_with_env(&manifest_dir, false, |name| explicit.get(name).cloned()).unwrap(),
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
            None,
            "CFG_OMIT_GIT_HASH must suppress even malformed ambient metadata and checkout fallback"
        );

        fs::remove_file(root.join("targo-trust/Cargo.toml")).unwrap();
        assert_eq!(trust_checkout_root(&manifest_dir), None);
        fs::remove_dir_all(root).unwrap();
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
