use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use std::{env, fs, io};

use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use trust_version::{
    BoundToolIdentity, BoundTools, DEFAULT_VERSION_SOURCE_PATH, Stage0Info, TrustVersionIdentity,
    VersionRuntime, parse_version_source, rust_compat_release, trust_archive_version,
};

use super::types::CANDIDATE_COMMAND_VERSION;
use crate::bounded_process;
use crate::input_limits::{MAX_RELEASE_METADATA_BYTES, read_bounded_utf8_file};

/// How long a release tool identity probe (a bound tool's `--version`, `-V` or
/// `-Vv`) waits for the tool's answer before reporting the tool unbound. The
/// self-verify harness's stage2 identity probes (Targo, `trustc` and `trustdoc`
/// `-Vv`, `trustd --version`) bind the same freshly built files and wait the same
/// guard (`self_verify_cli` `IDENTITY_PROBE_TIMEOUT`).
///
/// A hang detector, not a latency budget: a tool that is not hung answers its
/// version flag, so this bound only has to catch one that never will. It used
/// to be 10 s, which on macOS measured the host instead of the tool. The tools
/// these probes bind are files a build or an install has just written (stage2,
/// a fresh sysroot, a copied candidate), and a new executable's first exec,
/// scripts included, waits for syspolicyd's scan of it in one machine-wide
/// queue before its first instruction (docs/KNOWN_HAZARDS.md
/// EXEC-ASSESS-STALL-1); a repeat exec does not. Measured 2026-10-22 on an
/// 18-CPU macOS 26.6.2 host, fresh copies of bound tools: first exec 0.1-1.2 s
/// idle against 2-10 ms for a repeat; 29 s for a 0.6 MB `trustd` behind twelve
/// concurrent first execs of other fresh binaries at load 12-19; 55-57 s for
/// `trustd`, a one-`echo` script and a 230 MB `targo-trust` behind the same
/// queue at load 36. Behind that queue the 10 s bound reported 4-10 of the 12
/// tools of `version_cli`'s full-surface fixture `version-probe-failed`.
/// bounded_process.rs records a 273-275 s barrier for one-`echo` scripts. Ten
/// minutes sits over twice that barrier and ten times this host's measured
/// queue: a hung tool now takes that long to be reported, and a slow scan no
/// longer rejects a correct tool. The identity checks around the probe (hash
/// before and after, the same-file snapshot, the output bound) do not depend
/// on how long the answer took.
///
/// Two consequences of the size. In a `cfg(test)` build `bounded_process::output`
/// stretches this 180-fold, to 30 h, so no unit test may drive a hung tool through
/// these probe sites; a test of the deadline itself passes a tiny bound to
/// `bounded_process::output_with_exact_deadline`. And `bound_tools` probes its
/// 13 tools one after another, so a host where every tool hangs reports after
/// 13 times this bound; a caller with a shorter outer bound (trustc_native's 2 h
/// capture of `targo trust version`) fails closed on its own timeout first. No
/// progress line is printed meanwhile: `targo trust version` keeps its stderr
/// empty (tests/version_cli.rs asserts it).
pub(crate) const TOOL_IDENTITY_PROBE_HANG_GUARD: Duration = Duration::from_secs(10 * 60);

pub(super) fn build_version_identity(
    explicit_root: Option<&Path>,
) -> io::Result<TrustVersionIdentity> {
    let root = discover_repo_root(explicit_root)?;
    let source_text = read_bounded_utf8_file(
        &root.join(DEFAULT_VERSION_SOURCE_PATH),
        MAX_RELEASE_METADATA_BYTES,
    )?;
    let source = parse_version_source(&source_text)
        .map_err(|err| io::Error::new(io::ErrorKind::InvalidData, err))?;

    // Trust states two version lines in two files, deliberately:
    //
    //   src/rust-compat-version  the Rust release the `-V` protocol reports
    //   src/version              Trust's own MAJOR.MINOR.0 — a mirror of the ONE
    //                            authority, the root Cargo.toml
    //                            `[workspace.package] version`, written only by
    //                            `scripts/trust_version_sync.py --write` (bootstrap
    //                            refuses to build on drift; `crates/trust-version`'s
    //                            `every_version_mirror_agrees_with_the_authority`
    //                            test fails on it)
    //
    // The bound-tool surface below measures every tool by the line it PRINTS for
    // `--version`, which bootstrap stamps from the compat file; reading Trust's
    // own version here instead is what made a correct `trustd 1.99.0-dev` fail
    // its identity binding against an expected `trustd 0.1.0-dev`. Archives keep
    // being named from Trust's own version, which is the other half of the split.
    let rust_upstream_version =
        read_trimmed(root.join("src/rust-compat-version")).unwrap_or_else(|| "unknown".to_string());
    let trust_product_version =
        read_trimmed(root.join("src/version")).unwrap_or_else(|| "unknown".to_string());
    let bootstrap_channel =
        read_trimmed(root.join("src/ci/channel")).unwrap_or_else(|| "unknown".to_string());
    let rust_compat_version = rust_compat_release(&rust_upstream_version, &bootstrap_channel);
    let archive_version = trust_archive_version(&trust_product_version, &bootstrap_channel);
    let candidate_commit = crate::controlled_git::canonical_head(
        &root,
        "release repository HEAD probe",
        64 * 1024,
        Duration::from_secs(10),
    )
    .ok();
    let commit_date = git_output(&root, &["log", "-1", "--format=%cs"]);
    let current_exe = env::current_exe().ok();
    let tools = bound_tools(current_exe.as_deref(), &rust_compat_version);

    Ok(TrustVersionIdentity::from_source_and_runtime(
        source,
        VersionRuntime {
            rust_upstream_version,
            bootstrap_channel,
            rust_compat_version,
            rust_compat_source: "src/rust-compat-version + src/ci/channel".to_string(),
            archive_version,
            candidate_commit,
            commit_date,
            host: host_label(),
            runner_kind: runner_kind(current_exe.as_deref()),
            candidate_command: "targo trust version --json".to_string(),
            candidate_command_version: CANDIDATE_COMMAND_VERSION,
            tools,
            stage0: stage0_info(&root),
        },
    ))
}

pub(super) fn discover_repo_root(explicit_root: Option<&Path>) -> io::Result<PathBuf> {
    if let Some(root) = explicit_root {
        let root = fs::canonicalize(root)?;
        if !root.is_dir() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("repository root is not a directory: {}", root.display()),
            ));
        }
        return Ok(root);
    }

    let mut current = env::current_dir()?;
    loop {
        if current.join(DEFAULT_VERSION_SOURCE_PATH).is_file()
            && current.join("src/version").is_file()
        {
            return fs::canonicalize(current);
        }
        if !current.pop() {
            return env::current_dir();
        }
    }
}

pub(super) fn bound_tools(current_exe: Option<&Path>, rust_compat_version: &str) -> BoundTools {
    let exe_dir = current_exe.and_then(Path::parent);
    BoundTools {
        frontend: bound_sibling_tool("targo", exe_dir, &["-V"], Some(rust_compat_version)),
        extension: bound_current_tool("targo-trust", current_exe, &["--version"], None),
        compiler: bound_sibling_tool("trustc", exe_dir, &["-Vv"], Some(rust_compat_version)),
        documentation: bound_sibling_tool(
            "trustdoc",
            exe_dir,
            &["--version"],
            Some(rust_compat_version),
        ),
        formatter: bound_sibling_tool(
            "trustfmt",
            exe_dir,
            &["--version"],
            Some(rust_compat_version),
        ),
        cargo_formatter: bound_sibling_tool(
            "targo-fmt",
            exe_dir,
            &["--version"],
            Some(rust_compat_version),
        ),
        tippy: bound_sibling_tool("tippy", exe_dir, &["--version"], Some(rust_compat_version)),
        targo_tippy: bound_sibling_tool(
            "targo-tippy",
            exe_dir,
            &["--version"],
            Some(rust_compat_version),
        ),
        tippy_driver: bound_sibling_tool(
            "tippy-driver",
            exe_dir,
            &["--version"],
            Some(rust_compat_version),
        ),
        analyzer: bound_sibling_tool(
            "trust-analyzer",
            exe_dir,
            &["--version"],
            Some(rust_compat_version),
        ),
        daemon: bound_sibling_tool("trustd", exe_dir, &["--version"], Some(rust_compat_version)),
        miri: bound_sibling_tool("trust-miri", exe_dir, &["--version"], Some(rust_compat_version)),
        targo_miri: bound_sibling_tool(
            "targo-miri",
            exe_dir,
            &["--version"],
            Some(rust_compat_version),
        ),
    }
}

fn bound_sibling_tool(
    name: &str,
    exe_dir: Option<&Path>,
    version_args: &[&str],
    rust_compat_version: Option<&str>,
) -> BoundToolIdentity {
    bound_tool(name, resolve_tool_path(exe_dir, name), version_args, rust_compat_version)
}

fn bound_current_tool(
    name: &str,
    current_exe: Option<&Path>,
    version_args: &[&str],
    rust_compat_version: Option<&str>,
) -> BoundToolIdentity {
    bound_tool(name, current_exe.map(Path::to_path_buf), version_args, rust_compat_version)
}

pub(super) fn host_executable_name(tool: &str) -> String {
    format!("{tool}{}", env::consts::EXE_SUFFIX)
}

fn resolve_tool_path(exe_dir: Option<&Path>, sibling_name: &str) -> Option<PathBuf> {
    Some(exe_dir?.join(host_executable_name(sibling_name)))
}

fn bound_tool(
    name: &str,
    path: Option<PathBuf>,
    version_args: &[&str],
    rust_compat_version: Option<&str>,
) -> BoundToolIdentity {
    let Some(path) = path else {
        return BoundToolIdentity::missing(name);
    };

    let metadata = match fs::symlink_metadata(&path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return BoundToolIdentity::missing(name);
        }
        Err(_) => {
            return rejected_bound_tool(name, path, rust_compat_version, "unreadable");
        }
    };
    if metadata.file_type().is_symlink() {
        return rejected_bound_tool(name, path, rust_compat_version, "rejected-symlink");
    }
    if !metadata.file_type().is_file() {
        return rejected_bound_tool(name, path, rust_compat_version, "not-regular");
    }

    let executable = is_executable_metadata(&metadata);
    let Some(sha256_before) = bound_file_sha256(&path) else {
        return rejected_bound_tool(name, path, rust_compat_version, "unreadable");
    };
    let version_output = executable.then(|| command_output_text(&path, version_args)).flatten();
    let sha256 = bound_file_sha256(&path);
    let after = fs::symlink_metadata(&path).ok();
    if sha256.as_deref() != Some(sha256_before.as_str())
        || after.as_ref().is_none_or(|after| {
            after.file_type().is_symlink()
                || !after.file_type().is_file()
                || !same_file_snapshot(&metadata, after)
        })
    {
        return rejected_bound_tool(name, path, rust_compat_version, "changed-during-identity");
    }
    let version = version_output
        .as_deref()
        .and_then(|text| text.lines().next())
        .filter(|line| !line.trim().is_empty())
        .map(str::to_string);
    if executable && version.is_none() {
        return rejected_bound_tool(name, path, rust_compat_version, "version-probe-failed");
    }
    if name == "trustd"
        && !version_output.as_deref().is_some_and(|output| {
            trustd_version_output_is_bound(output, rust_compat_version.unwrap_or_default())
        })
    {
        return rejected_bound_tool(name, path, rust_compat_version, "invalid-trustd-identity");
    }
    let commit_hash = version_output.as_deref().and_then(parse_commit_hash);
    BoundToolIdentity {
        name: name.to_string(),
        path: Some(path.display().to_string()),
        sha256,
        executable: Some(executable),
        version,
        commit_hash,
        rust_compat_version: rust_compat_version.map(str::to_string),
        resolution: Some(if executable {
            "bound-executable".to_string()
        } else {
            "not-executable".to_string()
        }),
        rejected_inherited_name: None,
        rejected_path: None,
    }
}

fn rejected_bound_tool(
    name: &str,
    path: PathBuf,
    rust_compat_version: Option<&str>,
    resolution: &str,
) -> BoundToolIdentity {
    BoundToolIdentity {
        name: name.to_string(),
        path: Some(path.display().to_string()),
        sha256: None,
        executable: Some(false),
        version: None,
        commit_hash: None,
        rust_compat_version: rust_compat_version.map(str::to_string),
        resolution: Some(resolution.to_string()),
        rejected_inherited_name: None,
        rejected_path: None,
    }
}

fn command_output_text(path: &Path, args: &[&str]) -> Option<String> {
    let mut command = Command::new(path);
    command.args(args).env_clear();
    if let Some((variable, value)) = crate::pipeline::probe::native_runtime_environment(path) {
        command.env(variable, value);
    }
    let output = bounded_process::output(
        &mut command,
        &format!("release tool identity probe for {}", path.display()),
        64 * 1024,
        TOOL_IDENTITY_PROBE_HANG_GUARD,
    )
    .ok()?;
    if !output.status.success() {
        return None;
    }
    String::from_utf8(output.stdout).ok()
}

pub(super) fn file_sha256(path: &Path) -> Option<String> {
    exact_file_sha256_with_prefix(path, 0, None).map(|(sha256, _)| sha256)
}

/// Hash an exact regular file without following a leaf symlink.  Comparing
/// the file identity before and after the read prevents a path replacement
/// from producing a digest that is falsely attributed to the inspected leaf.
pub(super) fn bound_file_sha256(path: &Path) -> Option<String> {
    const MAX_BOUND_TOOL_BYTES: u64 = 1024 * 1024 * 1024;
    exact_file_sha256_with_prefix(path, 0, Some(MAX_BOUND_TOOL_BYTES)).map(|(sha256, _)| sha256)
}

/// Authenticate one immutable snapshot of an exact regular file, optionally
/// retaining a short prefix for format checks. The digest and prefix always
/// come from the same opened file identity.
pub(super) fn exact_file_sha256_with_prefix(
    path: &Path,
    prefix_len: usize,
    max_bytes: Option<u64>,
) -> Option<(String, Vec<u8>)> {
    let before = fs::symlink_metadata(path).ok()?;
    if before.file_type().is_symlink()
        || !before.file_type().is_file()
        || max_bytes.is_some_and(|max_bytes| before.len() > max_bytes)
    {
        return None;
    }
    let mut file = fs::File::open(path).ok()?;
    let opened = file.metadata().ok()?;
    if !opened.file_type().is_file() || !same_file_snapshot(&before, &opened) {
        return None;
    }
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    let initial_prefix_capacity =
        usize::try_from(before.len()).unwrap_or(prefix_len).min(prefix_len);
    let mut prefix = Vec::with_capacity(initial_prefix_capacity);
    let mut total = 0_u64;
    loop {
        let read = io::Read::read(&mut file, &mut buffer).ok()?;
        if read == 0 {
            break;
        }
        total = total.checked_add(read as u64)?;
        if total > before.len() || max_bytes.is_some_and(|max_bytes| total > max_bytes) {
            return None;
        }
        let retain = prefix_len.saturating_sub(prefix.len()).min(read);
        prefix.extend_from_slice(&buffer[..retain]);
        hasher.update(&buffer[..read]);
    }
    if total != before.len() {
        return None;
    }
    let opened_after = file.metadata().ok()?;
    let after = fs::symlink_metadata(path).ok()?;
    if after.file_type().is_symlink()
        || !after.file_type().is_file()
        || !same_file_snapshot(&before, &opened_after)
        || !same_file_snapshot(&before, &after)
    {
        return None;
    }
    Some((format!("{:x}", hasher.finalize()), prefix))
}

pub(super) fn is_executable_file(path: &Path) -> bool {
    let Ok(metadata) = fs::symlink_metadata(path) else {
        return false;
    };
    if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
        return false;
    }
    is_executable_metadata(&metadata)
}

/// Compatibility entrypoints (`cargo` -> `targo`, `rustc` -> `trustc`) are
/// intentionally links.  Their caller separately proves that the resolved
/// target remains inside the selected bin directory, so target-following is
/// appropriate only for that compatibility surface.
pub(super) fn is_executable_target(path: &Path) -> bool {
    fs::metadata(path)
        .ok()
        .filter(fs::Metadata::is_file)
        .is_some_and(|metadata| is_executable_metadata(&metadata))
}

pub(super) fn same_file_or_exact_contents(left: &Path, right: &Path) -> bool {
    let Some(left) = fs::canonicalize(left).ok() else {
        return false;
    };
    let Some(right) = fs::canonicalize(right).ok() else {
        return false;
    };
    if left == right {
        return true;
    }
    bound_file_sha256(&left)
        .zip(bound_file_sha256(&right))
        .is_some_and(|(left, right)| left == right)
}

#[cfg(unix)]
fn same_file_identity(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    use std::os::unix::fs::MetadataExt;

    left.dev() == right.dev() && left.ino() == right.ino()
}

#[cfg(unix)]
fn same_file_snapshot(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    use std::os::unix::fs::MetadataExt as _;

    same_file_identity(left, right)
        && left.len() == right.len()
        && left.mode() == right.mode()
        && left.mtime() == right.mtime()
        && left.mtime_nsec() == right.mtime_nsec()
        && left.ctime() == right.ctime()
        && left.ctime_nsec() == right.ctime_nsec()
}

#[cfg(not(unix))]
fn same_file_identity(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.is_file() && right.is_file() && left.len() == right.len()
}

#[cfg(not(unix))]
fn same_file_snapshot(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    same_file_identity(left, right)
        && left.len() == right.len()
        && left.modified().ok() == right.modified().ok()
}

#[cfg(unix)]
fn is_executable_metadata(metadata: &fs::Metadata) -> bool {
    use std::os::unix::fs::PermissionsExt;

    metadata.permissions().mode() & 0o111 != 0
}

#[cfg(not(unix))]
fn is_executable_metadata(metadata: &fs::Metadata) -> bool {
    metadata.is_file()
}

fn parse_commit_hash(version_output: &str) -> Option<String> {
    version_output.lines().find_map(|line| {
        let (key, value) = line.split_once(':')?;
        (key.trim() == "commit-hash" && is_hex_commit(value.trim()))
            .then(|| value.trim().to_string())
    })
}

pub(super) fn trustd_version_output_is_bound(
    version_output: &str,
    rust_compat_version: &str,
) -> bool {
    if rust_compat_version.is_empty() {
        return false;
    }
    let lines = version_output.lines().map(str::trim).collect::<Vec<_>>();
    let expected_first = format!("trustd {rust_compat_version}");
    let identities =
        lines.iter().filter_map(|line| line.strip_prefix("trust.identity=")).collect::<Vec<_>>();
    let protocols =
        lines.iter().filter_map(|line| line.strip_prefix("trust.protocol=")).collect::<Vec<_>>();
    let commits = lines
        .iter()
        .filter_map(|line| line.strip_prefix("commit-hash:").map(str::trim))
        .collect::<Vec<_>>();
    lines.first().copied() == Some(expected_first.as_str())
        && identities == ["trustd"]
        && protocols == [trust_router::coordinator::STATUS_VERSION]
        && commits.len() == 1
        && is_canonical_commit(commits[0])
        && {
            let legacy = lines
                .iter()
                .filter_map(|line| line.strip_prefix("trust-repo-commit-hash:").map(str::trim))
                .collect::<Vec<_>>();
            legacy.is_empty() || legacy == commits
        }
}

fn is_canonical_commit(value: &str) -> bool {
    value.len() == 40
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn is_hex_commit(value: &str) -> bool {
    value.len() == 40 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn stage0_info(root: &Path) -> Option<Stage0Info> {
    let sha_path = root.join("bootstrap/trust-stage0/dist/channel-rust-trust.toml.sha256");
    let channel_manifest_sha256 = read_trimmed(sha_path)
        .map(|text| text.split_whitespace().next().unwrap_or(text.as_str()).to_string());

    channel_manifest_sha256.map(|sha256| Stage0Info {
        source: "bootstrap/trust-stage0".to_string(),
        channel_manifest_sha256: Some(sha256),
    })
}

pub(super) fn read_trimmed(path: impl AsRef<Path>) -> Option<String> {
    read_bounded_utf8_file(path.as_ref(), MAX_RELEASE_METADATA_BYTES)
        .ok()
        .map(|text| text.trim().to_string())
        .filter(|text| !text.is_empty())
}

pub(super) fn generated_at_unix_seconds() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_secs())
        .unwrap_or_default()
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum RepositoryStatus {
    Clean,
    Dirty(Vec<String>),
    Unavailable(String),
}

impl RepositoryStatus {
    pub(super) fn is_dirty_or_unavailable(&self) -> bool {
        !matches!(self, Self::Clean)
    }

    pub(super) fn metadata(&self) -> Value {
        match self {
            Self::Clean => status_metadata(Vec::new()),
            Self::Dirty(lines) => status_metadata(lines.clone()),
            Self::Unavailable(error) => json!({
                "available": false,
                "dirty": null,
                "porcelain_v1": [],
                "error": error,
            }),
        }
    }
}

fn status_metadata(lines: Vec<String>) -> Value {
    json!({
        "available": true,
        "dirty": !lines.is_empty(),
        "porcelain_v1": lines,
        "untracked_files": "all",
        "ignore_submodules": "none",
    })
}

pub(super) fn repository_status(root: &Path, candidate_commit: Option<&str>) -> RepositoryStatus {
    let context = "release repository status probe";
    capture_repository_status(
        candidate_commit,
        || crate::controlled_git::canonical_head(root, context, 64 * 1024, Duration::from_secs(10)),
        || {
            crate::controlled_git::exact_status_porcelain_v1(
                root,
                context,
                1024 * 1024,
                Duration::from_secs(30),
            )
        },
    )
}

fn capture_repository_status(
    candidate_commit: Option<&str>,
    mut head: impl FnMut() -> Result<String, String>,
    mut status: impl FnMut() -> Result<Vec<String>, String>,
) -> RepositoryStatus {
    let Some(candidate_commit) = candidate_commit else {
        return RepositoryStatus::Unavailable("candidate HEAD is unavailable".to_string());
    };
    let check_head = |head: &mut dyn FnMut() -> Result<String, String>| -> Result<(), String> {
        let actual = head()?;
        if actual != candidate_commit {
            return Err(format!(
                "repository HEAD changed from candidate {candidate_commit} to {actual}"
            ));
        }
        Ok(())
    };

    // A single status invocation is not an atomic worktree snapshot. A second
    // bounded scan catches a change during status collection.
    let result = (|| {
        check_head(&mut head)?;
        let first = status()?;
        check_head(&mut head)?;
        let second = status()?;
        check_head(&mut head)?;
        if first != second {
            return Err("repository status changed between release probes".to_string());
        }
        Ok(first)
    })();
    match result {
        Ok(lines) if lines.is_empty() => RepositoryStatus::Clean,
        Ok(lines) => RepositoryStatus::Dirty(lines),
        Err(error) => RepositoryStatus::Unavailable(error),
    }
}

fn git_output(root: &Path, args: &[&str]) -> Option<String> {
    crate::controlled_git::text(
        root,
        args,
        "release repository identity probe",
        64 * 1024,
        Duration::from_secs(10),
    )
    .ok()
    .filter(|text| !text.is_empty())
}

fn runner_kind(current_exe: Option<&Path>) -> String {
    match current_exe.and_then(Path::to_str) {
        Some(path) if path.contains("/stage2/") || path.contains("\\stage2\\") => {
            "candidate-stage2".to_string()
        }
        Some(path) if path.contains("/stage3/") || path.contains("\\stage3\\") => {
            "candidate-stage3".to_string()
        }
        _ => "source-diagnostic".to_string(),
    }
}

fn host_label() -> String {
    format!("{}-{}", env::consts::ARCH, env::consts::OS)
}

pub(super) fn tool_identity_summary(tool: &BoundToolIdentity) -> String {
    let mut parts = vec![tool.name.clone()];
    if let Some(version) = &tool.version {
        parts.push(version.clone());
    }
    if let Some(path) = &tool.path {
        parts.push(path.clone());
    }
    if let Some(sha256) = &tool.sha256 {
        parts.push(format!("sha256:{sha256}"));
    }
    if let Some(resolution) = &tool.resolution {
        parts.push(format!("[{resolution}]"));
    }
    parts.join(" ")
}

pub(super) fn canonicalize_or_display(path: &Path) -> PathBuf {
    fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

pub(super) fn path_is_stage1_sysroot(path: &str) -> bool {
    Path::new(path).file_name().is_some_and(|name| name == "stage1")
}

pub(super) fn repo_relative_path(root: &Path, path_text: &str) -> Option<PathBuf> {
    let path = Path::new(path_text);
    if path_text.is_empty() || path.is_absolute() {
        return None;
    }
    if path.components().any(|component| {
        matches!(component, Component::ParentDir | Component::RootDir | Component::Prefix(_))
    }) {
        return None;
    }
    Some(root.join(path))
}

pub(super) fn option_value<'a>(arg: &'a str, option: &str) -> Option<&'a str> {
    arg.strip_prefix(option)?.strip_prefix('=')
}

#[cfg(all(test, unix))]
mod tests {
    use std::fs;
    use std::os::unix::fs::PermissionsExt;
    use std::path::Path;

    use super::{
        RepositoryStatus, bound_file_sha256, bound_tool, capture_repository_status,
        repository_status,
    };

    const TEST_COMMIT: &str = "0123456789abcdef0123456789abcdef01234567";

    fn write_executable(path: &Path, script: &str) {
        fs::write(path, script).expect("write tool fixture");
        fs::set_permissions(path, fs::Permissions::from_mode(0o755))
            .expect("make tool fixture executable");
    }

    #[test]
    fn stable_versioned_tool_is_bound() {
        let dir = tempfile::tempdir().expect("temporary tool directory");
        let path = dir.path().join("trustfmt");
        write_executable(&path, "#!/bin/sh\nprintf '%s\\n' 'trustfmt 1.96.0-dev'\n");

        let identity = bound_tool("trustfmt", Some(path.clone()), &["--version"], None);

        assert_eq!(identity.resolution.as_deref(), Some("bound-executable"));
        assert_eq!(identity.version.as_deref(), Some("trustfmt 1.96.0-dev"));
        assert_eq!(identity.sha256, bound_file_sha256(&path));
    }

    #[test]
    fn failed_or_empty_version_probe_is_not_bound() {
        let dir = tempfile::tempdir().expect("temporary tool directory");
        for (name, script) in [
            ("failed", "#!/bin/sh\nexit 7\n"),
            ("empty", "#!/bin/sh\nexit 0\n"),
            ("blank", "#!/bin/sh\nprintf ' \\n'\n"),
        ] {
            let path = dir.path().join(name);
            write_executable(&path, script);

            let identity = bound_tool("trustfmt", Some(path), &["--version"], None);

            assert_eq!(identity.resolution.as_deref(), Some("version-probe-failed"));
            assert_eq!(identity.executable, Some(false));
            assert!(identity.sha256.is_none());
            assert!(identity.version.is_none());
        }
    }

    #[test]
    fn same_byte_replacement_during_probe_is_not_bound() {
        let dir = tempfile::tempdir().expect("temporary tool directory");
        let path = dir.path().join("trustfmt");
        write_executable(
            &path,
            "#!/bin/sh\n/bin/cp \"$0\" \"$0.next\" || exit 1\n/bin/mv \"$0.next\" \"$0\" || exit 1\nprintf '%s\\n' 'trustfmt 1.96.0-dev'\n",
        );
        let before = bound_file_sha256(&path);

        let identity = bound_tool("trustfmt", Some(path.clone()), &["--version"], None);

        assert!(before.is_some());
        assert_eq!(bound_file_sha256(&path), before);
        assert_eq!(identity.resolution.as_deref(), Some("changed-during-identity"));
        assert_eq!(identity.executable, Some(false));
        assert!(identity.sha256.is_none());
    }

    #[test]
    fn executable_mode_change_during_probe_is_not_bound() {
        let dir = tempfile::tempdir().expect("temporary tool directory");
        let path = dir.path().join("trustfmt");
        write_executable(
            &path,
            "#!/bin/sh\n/bin/chmod a-x \"$0\" || exit 1\nprintf '%s\\n' 'trustfmt 1.96.0-dev'\n",
        );
        let before = bound_file_sha256(&path);

        let identity = bound_tool("trustfmt", Some(path.clone()), &["--version"], None);

        assert_eq!(bound_file_sha256(&path), before);
        assert_eq!(identity.resolution.as_deref(), Some("changed-during-identity"));
        assert_eq!(identity.executable, Some(false));
    }

    #[test]
    fn stable_repository_status_has_one_consistent_dirty_snapshot() {
        for lines in [Vec::new(), vec!["?? new.txt".to_string()]] {
            let mut heads = 0;
            let mut scans = 0;
            let snapshot = capture_repository_status(
                Some(TEST_COMMIT),
                || {
                    heads += 1;
                    Ok(TEST_COMMIT.to_string())
                },
                || {
                    scans += 1;
                    Ok(lines.clone())
                },
            );
            assert_eq!(heads, 3);
            assert_eq!(scans, 2);
            assert_eq!(snapshot.is_dirty_or_unavailable(), !lines.is_empty());
            let metadata = snapshot.metadata();
            assert_eq!(metadata["available"], true);
            assert_eq!(metadata["dirty"], !lines.is_empty());
            assert_eq!(metadata["porcelain_v1"], serde_json::json!(lines));
        }
    }

    #[test]
    fn changing_status_in_either_direction_cannot_report_clean() {
        for (first, second) in [
            (Vec::new(), vec!["?? new.txt".to_string()]),
            (vec!["?? new.txt".to_string()], Vec::new()),
            (vec!["?? first.txt".to_string()], vec!["?? second.txt".to_string()]),
        ] {
            let mut scans = vec![first, second].into_iter();
            let snapshot = capture_repository_status(
                Some(TEST_COMMIT),
                || Ok(TEST_COMMIT.to_string()),
                || Ok(scans.next().expect("bounded second scan")),
            );
            assert!(matches!(snapshot, RepositoryStatus::Unavailable(_)));
            assert!(snapshot.is_dirty_or_unavailable());
            assert_eq!(snapshot.metadata()["available"], false);
            assert_eq!(snapshot.metadata()["dirty"], serde_json::Value::Null);
        }
    }

    #[test]
    fn changed_or_unavailable_head_and_status_fail_closed() {
        let mut heads = [TEST_COMMIT, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"].into_iter();
        let changed_head = capture_repository_status(
            Some(TEST_COMMIT),
            || Ok(heads.next().expect("second HEAD probe").to_string()),
            || Ok(Vec::new()),
        );
        assert!(matches!(changed_head, RepositoryStatus::Unavailable(_)));

        let failed_status = capture_repository_status(
            Some(TEST_COMMIT),
            || Ok(TEST_COMMIT.to_string()),
            || Err("Git authority unavailable".to_string()),
        );
        assert!(matches!(failed_status, RepositoryStatus::Unavailable(_)));
        assert_eq!(failed_status.metadata()["available"], false);
        assert!(failed_status.is_dirty_or_unavailable());

        let root = tempfile::tempdir().expect("non-Git directory");
        let no_git = repository_status(root.path(), Some(TEST_COMMIT));
        assert!(matches!(no_git, RepositoryStatus::Unavailable(_)));
        assert!(no_git.is_dirty_or_unavailable());
    }
}
