use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use std::{env, fs, io};

use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use trust_version::{
    BoundToolIdentity, BoundTools, DEFAULT_VERSION_SOURCE_PATH, Stage0Info, TrustVersionIdentity,
    VersionRuntime, parse_version_source,
};

use crate::bounded_process;
use crate::input_limits::{MAX_RELEASE_METADATA_BYTES, read_bounded_utf8_file};

use super::types::CANDIDATE_COMMAND_VERSION;

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

    let rust_upstream_version =
        read_trimmed(root.join("src/version")).unwrap_or_else(|| "unknown".to_string());
    let bootstrap_channel =
        read_trimmed(root.join("src/ci/channel")).unwrap_or_else(|| "unknown".to_string());
    let rust_compat_version = rust_compat_version(&rust_upstream_version, &bootstrap_channel);
    let archive_version = archive_version(&rust_upstream_version, &bootstrap_channel);
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
            rust_compat_source: "src/version + src/ci/channel".to_string(),
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
    if sha256.as_deref() != Some(sha256_before.as_str()) {
        return rejected_bound_tool(name, path, rust_compat_version, "changed-during-identity");
    }
    if name == "trustd"
        && !version_output.as_deref().is_some_and(|output| {
            trustd_version_output_is_bound(output, rust_compat_version.unwrap_or_default())
        })
    {
        return rejected_bound_tool(name, path, rust_compat_version, "invalid-trustd-identity");
    }
    let version =
        version_output.as_deref().and_then(|text| text.lines().next().map(str::to_string));
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
        Duration::from_secs(10),
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

pub(super) fn repo_dirty(root: &Path) -> bool {
    git_status_porcelain_lines(root).map(|lines| !lines.is_empty()).unwrap_or(true)
}

pub(super) fn repo_dirty_metadata(root: &Path) -> Value {
    let Some(lines) = git_status_porcelain_lines(root) else {
        return json!({"available": false, "dirty": null, "porcelain_v1": []});
    };
    json!({
        "available": true,
        "dirty": !lines.is_empty(),
        "porcelain_v1": lines,
        "untracked_files": "all",
        "ignore_submodules": "none",
    })
}

fn git_status_porcelain_lines(root: &Path) -> Option<Vec<String>> {
    crate::controlled_git::exact_status_porcelain_v1(
        root,
        "release repository status probe",
        1024 * 1024,
        Duration::from_secs(30),
    )
    .ok()
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

fn rust_compat_version(rust_upstream_version: &str, bootstrap_channel: &str) -> String {
    match bootstrap_channel {
        "stable" => rust_upstream_version.to_string(),
        "trust" => format!("{rust_upstream_version}-dev"),
        channel => format!("{rust_upstream_version}-{channel}"),
    }
}

fn archive_version(rust_upstream_version: &str, bootstrap_channel: &str) -> String {
    match bootstrap_channel {
        "trust" => format!("{rust_upstream_version}-trust"),
        "stable" => rust_upstream_version.to_string(),
        channel => format!("{rust_upstream_version}-{channel}"),
    }
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
