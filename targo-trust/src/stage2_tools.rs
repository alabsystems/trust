//! Bounded, deterministic discovery of repository-local stage2 tools.
//!
//! A repository-local path is not an authenticated tool identity.  The
//! snapshot API below binds the canonical regular-file path, length, and
//! SHA-256 before a caller launches it, and lets the caller repeat that check
//! after use.  On Unix it additionally binds the opened file object by device
//! and inode.  Non-Unix targets have no stable file-object identifier in this
//! module, so they provide path/length/content endpoint checks only.  These
//! checks detect persistent replacement and ordinary races, but deliberately
//! do not claim to bind the bytes the kernel maps for `exec`: a same-user
//! swap/execute/restore race still requires execution isolation or an
//! authenticated platform handle outside this module.

use std::fs::OpenOptions;
use std::io::Read as _;
use std::path::{Component, Path, PathBuf};
use std::{env, fs, io};

use sha2::{Digest as _, Sha256};

const MAX_STAGE2_TOOL_BYTES: u64 = 1024 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExactExecutableIdentity {
    canonical_path: PathBuf,
    sha256: String,
    len: u64,
    file_id: ExactFileId,
}

pub(crate) type RepoStage2ToolIdentity = ExactExecutableIdentity;

#[cfg(unix)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ExactFileId {
    device: u64,
    inode: u64,
}

#[cfg(not(unix))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ExactFileId;

#[cfg(unix)]
fn exact_file_id(metadata: &fs::Metadata) -> ExactFileId {
    use std::os::unix::fs::MetadataExt as _;

    ExactFileId { device: metadata.dev(), inode: metadata.ino() }
}

#[cfg(not(unix))]
fn exact_file_id(_metadata: &fs::Metadata) -> ExactFileId {
    ExactFileId
}

pub(crate) fn host_executable_name(tool: &str) -> String {
    format!("{tool}{}", env::consts::EXE_SUFFIX)
}

fn canonical_tool_filename(path: &Path, tool: &str) -> bool {
    path.file_name().is_some_and(|name| name == std::ffi::OsStr::new(&host_executable_name(tool)))
}

fn path_is_repo_stage2_tool(repo_root: &Path, path: &Path, tool: &str) -> bool {
    let Ok(relative) = path.strip_prefix(repo_root) else {
        return false;
    };
    let Some(components) = relative
        .components()
        .map(|component| match component {
            Component::Normal(value) => value.to_str(),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    components.len() == 5
        && components[0] == "build"
        && !components[1].is_empty()
        && components[2] == "stage2"
        && components[3] == "bin"
        && components[4] == host_executable_name(tool)
}

#[cfg(unix)]
fn metadata_is_executable(metadata: &fs::Metadata) -> bool {
    use std::os::unix::fs::PermissionsExt as _;

    metadata.permissions().mode() & 0o111 != 0
}

#[cfg(not(unix))]
fn metadata_is_executable(metadata: &fs::Metadata) -> bool {
    metadata.is_file()
}

/// Validate one exact `build/<host>/stage2/bin/<tool>` leaf without following
/// any caller-writable symlink component.
pub(crate) fn validate_repo_stage2_tool(
    repo_root: &Path,
    path: &Path,
    source: &str,
    tool: &str,
) -> Result<PathBuf, String> {
    snapshot_repo_stage2_tool(repo_root, path, source, tool).map(|identity| identity.canonical_path)
}

/// Capture a bounded executable snapshot for one repository-local stage2
/// tool.  Callers that execute the tool as evidence should retain this value
/// and pass it to [`revalidate_repo_stage2_tool`] after the child exits.  The
/// snapshot includes file-object identity on Unix; non-Unix targets bind only
/// the canonical path, length, and content hash.
pub(crate) fn snapshot_repo_stage2_tool(
    repo_root: &Path,
    path: &Path,
    source: &str,
    tool: &str,
) -> Result<RepoStage2ToolIdentity, String> {
    if !canonical_tool_filename(path, tool) {
        return Err(format!("{source} must name canonical `{tool}`, not `{}`", path.display()));
    }

    let canonical_root = fs::canonicalize(repo_root).map_err(|error| {
        format!("{source} could not canonicalize repository root {}: {error}", repo_root.display())
    })?;
    let relative = path
        .strip_prefix(repo_root)
        .or_else(|_| path.strip_prefix(&canonical_root))
        .map_err(|_| {
            format!(
                "{source} must point at repo-local stage2 {tool} under build/*/stage2/bin/{}: {}",
                host_executable_name(tool),
                path.display()
            )
        })?;

    let mut prefix = canonical_root.clone();
    for component in relative.components() {
        if !matches!(component, Component::Normal(_)) {
            return Err(format!(
                "{source} stage2 {tool} path contains a non-normal component: {}",
                path.display()
            ));
        }
        prefix.push(component.as_os_str());
        let metadata = fs::symlink_metadata(&prefix).map_err(|error| {
            format!("{source} {tool} path is not accessible at {}: {error}", prefix.display())
        })?;
        if metadata.file_type().is_symlink() {
            return Err(format!(
                "{source} must not use symlinks for stage2 {tool} identity: {}",
                prefix.display()
            ));
        }
    }

    let canonical_path = fs::canonicalize(&prefix).map_err(|error| {
        format!("{source} could not canonicalize stage2 {tool} {}: {error}", path.display())
    })?;
    if !path_is_repo_stage2_tool(&canonical_root, &canonical_path, tool) {
        return Err(format!(
            "{source} must point at repo-local stage2 {tool} under build/*/stage2/bin/{}: {}",
            host_executable_name(tool),
            path.display()
        ));
    }
    let metadata = fs::symlink_metadata(&canonical_path).map_err(|error| {
        format!("{source} could not inspect stage2 {tool} {}: {error}", canonical_path.display())
    })?;
    if !metadata.file_type().is_file() {
        return Err(format!(
            "{source} {tool} is not an exact regular file: {}",
            canonical_path.display()
        ));
    }
    if !metadata_is_executable(&metadata) {
        return Err(format!(
            "{source} {tool} is not an executable file: {}",
            canonical_path.display()
        ));
    }
    snapshot_exact_executable(&canonical_path, source, &format!("stage2 {tool}"))
}

/// Re-open and re-hash a previously captured stage2 tool identity.
///
/// This is intentionally a before/after endpoint check.  It fails on path,
/// length, or content changes, and on Unix also fails on file-object changes.
/// Non-Unix targets do not provide a stable file-object identifier here.  No
/// target can exclude a transient replacement restored before this call.
pub(crate) fn revalidate_repo_stage2_tool(
    expected: &RepoStage2ToolIdentity,
    source: &str,
    tool: &str,
) -> Result<(), String> {
    let observed =
        snapshot_exact_executable(&expected.canonical_path, source, &format!("stage2 {tool}"))?;
    if observed != *expected {
        return Err(format!(
            "{source} stage2 {tool} changed after its identity was captured (expected sha256 {}, observed {}): {}",
            expected.sha256,
            observed.sha256,
            expected.canonical_path.display()
        ));
    }
    Ok(())
}

/// Capture one bounded regular-executable snapshot without following a
/// symlink leaf.  On Unix the snapshot includes device/inode identity; on
/// non-Unix targets it is limited to path/length/content endpoint checks.
/// Repository-shape validation, provenance authentication, and launch
/// isolation remain the caller's responsibility.
pub(crate) fn snapshot_exact_executable(
    path: &Path,
    source: &str,
    label: &str,
) -> Result<ExactExecutableIdentity, String> {
    let before = fs::symlink_metadata(path).map_err(|error| {
        format!("{source} could not inspect {label} {}: {error}", path.display())
    })?;
    if before.file_type().is_symlink() || !before.file_type().is_file() {
        return Err(format!("{source} {label} is not an exact regular file: {}", path.display()));
    }
    if before.len() == 0 || before.len() > MAX_STAGE2_TOOL_BYTES {
        return Err(format!(
            "{source} {label} size {} is outside the accepted 1..={MAX_STAGE2_TOOL_BYTES} byte range: {}",
            before.len(),
            path.display()
        ));
    }
    if !metadata_is_executable(&before) {
        return Err(format!("{source} {label} is not executable: {}", path.display()));
    }

    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW);
    }
    let mut file = options.open(path).map_err(|error| {
        format!("{source} could not open exact {label} {}: {error}", path.display())
    })?;
    let opened = file.metadata().map_err(|error| {
        format!("{source} could not inspect opened {label} {}: {error}", path.display())
    })?;
    if !opened.file_type().is_file()
        || opened.len() != before.len()
        || exact_file_id(&opened) != exact_file_id(&before)
    {
        return Err(format!(
            "{source} {label} changed while it was being opened: {}",
            path.display()
        ));
    }

    let mut hasher = Sha256::new();
    let copied = io::copy(&mut (&mut file).take(before.len().saturating_add(1)), &mut hasher)
        .map_err(|error| format!("{source} could not hash {label} {}: {error}", path.display()))?;
    if copied != before.len() {
        return Err(format!(
            "{source} {label} length changed while it was being hashed: {}",
            path.display()
        ));
    }
    let after = fs::symlink_metadata(path).map_err(|error| {
        format!("{source} could not re-inspect {label} {}: {error}", path.display())
    })?;
    if after.file_type().is_symlink()
        || !after.file_type().is_file()
        || after.len() != before.len()
        || exact_file_id(&after) != exact_file_id(&before)
    {
        return Err(format!(
            "{source} {label} changed while it was being hashed: {}",
            path.display()
        ));
    }

    Ok(ExactExecutableIdentity {
        canonical_path: path.to_path_buf(),
        sha256: format!("{:x}", hasher.finalize()),
        len: before.len(),
        file_id: exact_file_id(&before),
    })
}

/// Revalidate a generic executable snapshot after use, subject to the same
/// Unix-only file-object identity limitation as [`snapshot_exact_executable`].
pub(crate) fn revalidate_exact_executable(
    expected: &ExactExecutableIdentity,
    source: &str,
    label: &str,
) -> Result<(), String> {
    let observed = snapshot_exact_executable(&expected.canonical_path, source, label)?;
    if observed != *expected {
        return Err(format!(
            "{source} {label} changed after its identity was captured (expected sha256 {}, observed {}): {}",
            expected.sha256,
            observed.sha256,
            expected.canonical_path.display()
        ));
    }
    Ok(())
}

fn validate_candidate_if_present(
    repo_root: &Path,
    candidate: &Path,
    tool: &str,
) -> Result<Option<PathBuf>, String> {
    match fs::symlink_metadata(candidate) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(error) => {
            Err(format!("stage2 discovery could not inspect {}: {error}", candidate.display()))
        }
        Ok(_) => {
            validate_repo_stage2_tool(repo_root, candidate, "stage2 discovery", tool).map(Some)
        }
    }
}

/// Require one unique valid host directory rather than silently selecting
/// filesystem order. Bootstrap maintains `build/host` as a convenience
/// symlink on Unix; discovery deliberately ignores directory aliases and
/// returns the exact, non-symlinked host path they name.
pub(crate) fn discover_unique_repo_stage2_tool(
    repo_root: &Path,
    tool: &str,
) -> Result<Option<PathBuf>, String> {
    let executable = host_executable_name(tool);
    let build_dir = repo_root.join("build");
    let entries = match fs::read_dir(&build_dir) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => {
            return Err(format!(
                "stage2 discovery could not read {}: {error}",
                build_dir.display()
            ));
        }
    };
    let mut candidates = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|error| {
            format!("stage2 discovery could not inspect {}: {error}", build_dir.display())
        })?;
        let file_type = entry.file_type().map_err(|error| {
            format!("stage2 discovery could not inspect {}: {error}", entry.path().display())
        })?;
        // `build/host` is normally a bootstrap-created directory symlink. Do
        // not follow it (or any other alias) and then count the same tool twice;
        // the concrete host directory is considered below.
        if !file_type.is_dir() || file_type.is_symlink() {
            continue;
        }
        candidates.push(entry.path().join("stage2/bin").join(&executable));
    }
    candidates.sort();

    let mut valid = Vec::new();
    for candidate in candidates {
        if let Some(candidate) = validate_candidate_if_present(repo_root, &candidate, tool)? {
            valid.push(candidate);
        }
    }
    valid.sort();
    valid.dedup();
    match valid.as_slice() {
        [] => Ok(None),
        [only] => Ok(Some(only.clone())),
        many => Err(format!(
            "stage2 discovery found multiple `{tool}` executables ({}); use an explicit stage2 tool path",
            many.iter().map(|path| path.display().to_string()).collect::<Vec<_>>().join(", ")
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn executable(path: &Path) {
        fs::create_dir_all(path.parent().expect("tool parent")).expect("create tool parent");
        fs::write(path, b"tool").expect("write tool");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            fs::set_permissions(path, fs::Permissions::from_mode(0o700)).expect("chmod tool");
        }
    }

    #[test]
    fn exact_shape_and_unique_fallback_are_enforced() {
        let root = tempfile::tempdir().expect("stage2 fixture");
        let malformed =
            root.path().join("build/a/stage2/bin/nested").join(host_executable_name("trustc"));
        executable(&malformed);
        assert!(validate_repo_stage2_tool(root.path(), &malformed, "test", "trustc").is_err());

        let first = root.path().join("build/a/stage2/bin").join(host_executable_name("trustc"));
        let second = root.path().join("build/b/stage2/bin").join(host_executable_name("trustc"));
        executable(&first);
        executable(&second);
        let error = discover_unique_repo_stage2_tool(root.path(), "trustc")
            .expect_err("ambiguous nonpreferred stage2 tools must fail");
        assert!(error.contains("multiple `trustc`"), "{error}");

        fs::remove_dir_all(root.path().join("build/a")).expect("remove first candidate");
        fs::remove_dir_all(root.path().join("build/b")).expect("remove second candidate");
        let only =
            root.path().join("build/actual-host/stage2/bin").join(host_executable_name("trustc"));
        executable(&only);
        assert_eq!(
            discover_unique_repo_stage2_tool(root.path(), "trustc").expect("unique discovery"),
            Some(only.canonicalize().expect("canonical unique tool"))
        );
    }

    #[test]
    fn exact_identity_detects_persistent_replacement() {
        let root = tempfile::tempdir().expect("stage2 identity fixture");
        let tool =
            root.path().join("build/actual-host/stage2/bin").join(host_executable_name("trustc"));
        executable(&tool);
        let identity = snapshot_repo_stage2_tool(root.path(), &tool, "test", "trustc")
            .expect("capture exact identity");
        assert_eq!(identity.canonical_path, tool.canonicalize().expect("canonical tool"));
        assert_eq!(identity.sha256.len(), 64);
        revalidate_repo_stage2_tool(&identity, "test", "trustc")
            .expect("unchanged tool remains valid");

        fs::write(&tool, b"replacement").expect("replace tool bytes");
        let error = revalidate_repo_stage2_tool(&identity, "test", "trustc")
            .expect_err("replacement must fail exact identity");
        assert!(error.contains("changed after its identity was captured"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_leaf_and_directory_fail_closed() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().expect("stage2 symlink fixture");
        let real = root.path().join("real");
        executable(&real);
        let leaf = root.path().join("build/a/stage2/bin").join(host_executable_name("targo"));
        fs::create_dir_all(leaf.parent().expect("leaf parent")).expect("create leaf parent");
        symlink(&real, &leaf).expect("link leaf");
        assert!(discover_unique_repo_stage2_tool(root.path(), "targo").is_err());

        fs::remove_file(&leaf).expect("remove redirected leaf");
        executable(&leaf);
        symlink(root.path().join("build/a"), root.path().join("build/host"))
            .expect("link bootstrap host alias");
        let second = root.path().join("build/b/stage2/bin").join(host_executable_name("targo"));
        executable(&second);
        assert!(
            discover_unique_repo_stage2_tool(root.path(), "targo")
                .expect_err("host alias must not hide a second real host")
                .contains("multiple `targo`")
        );
        fs::remove_dir_all(root.path().join("build/b")).expect("remove second real host");
        assert_eq!(
            discover_unique_repo_stage2_tool(root.path(), "targo")
                .expect("directory aliases are ignored"),
            Some(leaf.canonicalize().expect("canonical concrete tool"))
        );
    }
}
