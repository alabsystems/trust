//! Fixed-authority Git probes for evidence and release metadata.
//!
//! Evidence producers must not resolve `git` through `PATH` or inherit Git
//! configuration from the invoking process.  This module centralizes the
//! closed environment and repository-local overrides used by those probes.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Output};
use std::time::Duration;

#[cfg(unix)]
use std::os::unix::fs::{MetadataExt, PermissionsExt};

use crate::bounded_process;

// `/usr/bin/git` on macOS is a libxcselect tool shim rather than Git itself.
// Under concurrent Stage2 tests that shim has dispatched `clang` for a Git
// invocation.  Evidence probes therefore execute the fixed real developer
// Git binary, never the basename-sensitive shim.
#[cfg(target_os = "macos")]
const SYSTEM_GIT_CANDIDATES: &[&str] = &[
    "/Library/Developer/CommandLineTools/usr/bin/git",
    "/Applications/Xcode.app/Contents/Developer/usr/bin/git",
];
#[cfg(not(target_os = "macos"))]
const SYSTEM_GIT_CANDIDATES: &[&str] = &["/usr/bin/git", "/bin/git"];
const MAX_LOCAL_EXCLUDE_BYTES: u64 = 64 * 1024;
// Trust currently has roughly 416,000 tracked paths.  Index-wide authority
// probes are intentionally bounded independently from the caller's status
// output budget: the stage inventory is about 47 MiB and `ls-files -v` is
// about 27 MiB in the real repository.  Keep ample, explicit headroom while
// still failing closed on an unexpectedly enormous or malformed index.
const MAX_INDEX_INVENTORY_BYTES: usize = 128 * 1024 * 1024;
const MAX_INDEX_ENTRIES: usize = 1_000_000;
const MAX_INDEX_RECORD_BYTES: usize = 16 * 1024;
const MAX_RECURSIVE_WORKTREES: usize = 1024;
const MAX_CONFIG_INVENTORY_BYTES: usize = 4 * 1024 * 1024;
// A content-authoritative pass reads every tracked byte. Trust currently has
// roughly 415,758 tracked paths / 3.75 GiB and takes about 27 seconds warm on
// the reference Apple Silicon checkout. Give cold and slower disks explicit
// headroom independently from the caller's small metadata-probe timeout.
const TRACKED_CONTENT_TIMEOUT: Duration = Duration::from_secs(5 * 60);

/// Resolve only a fixed operating-system Git executable.
pub(crate) fn executable() -> Result<PathBuf, String> {
    let mut rejected = Vec::new();
    for candidate in SYSTEM_GIT_CANDIDATES {
        let candidate = Path::new(candidate);
        match trusted_system_executable(candidate) {
            Ok(canonical) => return Ok(canonical),
            Err(error) => rejected.push(error),
        }
    }
    Err(format!(
        "no immutable root-owned Git executable exists at any fixed candidate: {}; rejections: {}",
        SYSTEM_GIT_CANDIDATES.join(", "),
        rejected.join("; ")
    ))
}

/// Validate both the spelling-time and resolved authority chains for a fixed
/// system executable. Checking only the leaf allows a root-owned binary below a
/// group-writable directory (notably the default root:admin 0775 `/Applications`
/// on macOS) to be replaced by another group member. The returned canonical path
/// is safe to execute because every ancestor and the target are root-owned and
/// non-writable by group/other.
#[cfg(unix)]
fn trusted_system_executable(candidate: &Path) -> Result<PathBuf, String> {
    if !candidate.is_absolute()
        || candidate
            .components()
            .any(|component| !matches!(component, Component::RootDir | Component::Normal(_)))
    {
        return Err(format!(
            "controlled Git candidate is not a normalized absolute path: {}",
            candidate.display()
        ));
    }

    let lexical_parent = candidate.parent().ok_or_else(|| {
        format!("controlled Git candidate has no parent: {}", candidate.display())
    })?;
    validate_root_owned_immutable_directory_chain(lexical_parent, "lexical")?;

    let lexical = fs::symlink_metadata(candidate).map_err(|error| {
        format!("could not inspect controlled Git candidate {}: {error}", candidate.display())
    })?;
    if !lexical.file_type().is_symlink() {
        validate_root_owned_executable(&lexical, candidate, "lexical")?;
    }

    let canonical = fs::canonicalize(candidate).map_err(|error| {
        format!("could not canonicalize controlled Git {}: {error}", candidate.display())
    })?;
    if !canonical.is_absolute() {
        return Err(format!(
            "controlled Git {} resolved to a non-absolute path {}",
            candidate.display(),
            canonical.display()
        ));
    }
    let canonical_parent = canonical.parent().ok_or_else(|| {
        format!("canonical controlled Git has no parent: {}", canonical.display())
    })?;
    validate_root_owned_immutable_directory_chain(canonical_parent, "canonical")?;
    let target = fs::symlink_metadata(&canonical).map_err(|error| {
        format!("could not inspect canonical controlled Git {}: {error}", canonical.display())
    })?;
    validate_root_owned_executable(&target, &canonical, "canonical")?;
    Ok(canonical)
}

#[cfg(not(unix))]
fn trusted_system_executable(candidate: &Path) -> Result<PathBuf, String> {
    Err(format!(
        "controlled system Git authority is unsupported on {}: {}",
        std::env::consts::OS,
        candidate.display()
    ))
}

#[cfg(unix)]
fn validate_root_owned_immutable_directory_chain(
    parent: &Path,
    spelling: &str,
) -> Result<(), String> {
    for directory in parent.ancestors() {
        let metadata = fs::symlink_metadata(directory).map_err(|error| {
            format!(
                "could not inspect {spelling} controlled Git ancestor {}: {error}",
                directory.display()
            )
        })?;
        if !metadata.file_type().is_dir()
            || metadata.uid() != 0
            || metadata.permissions().mode() & 0o022 != 0
        {
            return Err(format!(
                "{spelling} controlled Git ancestor must be a root-owned directory not writable by group/other: {}",
                directory.display()
            ));
        }
    }
    Ok(())
}

#[cfg(unix)]
fn validate_root_owned_executable(
    metadata: &fs::Metadata,
    path: &Path,
    spelling: &str,
) -> Result<(), String> {
    if !metadata.file_type().is_file()
        || metadata.uid() != 0
        || metadata.permissions().mode() & 0o111 == 0
        || metadata.permissions().mode() & 0o022 != 0
    {
        return Err(format!(
            "{spelling} controlled Git must be a root-owned executable regular file not writable by group/other: {}",
            path.display()
        ));
    }
    Ok(())
}

/// Discover and validate the canonical worktree containing `requested`.
pub(crate) fn resolve_repo_root(requested: &Path) -> Result<PathBuf, String> {
    let requested = fs::canonicalize(requested).map_err(|error| {
        format!("could not canonicalize repository path {}: {error}", requested.display())
    })?;
    if !requested.is_dir() {
        return Err(format!("repository path is not a directory: {}", requested.display()));
    }

    let root = requested
        .ancestors()
        .find_map(|candidate| match valid_git_marker(candidate) {
            Ok(true) => Some(Ok(candidate.to_path_buf())),
            Ok(false) => None,
            Err(error) => Some(Err(error)),
        })
        .transpose()?
        .ok_or_else(|| format!("no Git worktree contains {}", requested.display()))?;

    let discovered = text(
        &root,
        &["rev-parse", "--show-toplevel"],
        "controlled Git repository-root probe",
        64 * 1024,
        Duration::from_secs(30),
    )?;
    let discovered = fs::canonicalize(&discovered).map_err(|error| {
        format!("controlled Git returned an invalid worktree root `{discovered}`: {error}")
    })?;
    if discovered != root {
        return Err(format!(
            "controlled Git worktree mismatch: marker root {} but Git reported {}",
            root.display(),
            discovered.display()
        ));
    }
    Ok(root)
}

/// Construct a Git command with a fixed executable, closed environment, and
/// explicit worktree semantics. `root` must name a canonical worktree root.
pub(crate) fn command(root: &Path) -> Result<Command, String> {
    command_with_pathspec_mode(root, "--literal-pathspecs")
}

/// Construct a controlled Git command for subcommands, such as
/// `check-ignore`, whose operands are pathnames and which reject Git's global
/// pathspec-mode options.
///
/// Callers must use this only with subcommands that define their operands as
/// literal pathnames rather than pathspecs.
pub(crate) fn pathname_command(root: &Path) -> Result<Command, String> {
    command_with_pathspec_mode(root, "")
}

fn command_with_pathspec_mode(root: &Path, pathspec_mode: &str) -> Result<Command, String> {
    let root = fs::canonicalize(root).map_err(|error| {
        format!("could not canonicalize controlled Git root {}: {error}", root.display())
    })?;
    if !root.is_dir() || !valid_git_marker(&root)? {
        return Err(format!("controlled Git root is not a worktree root: {}", root.display()));
    }
    let worktree = root
        .to_str()
        .ok_or_else(|| "controlled Git requires a UTF-8 repository path".to_string())?;
    let git_dir = resolve_git_dir(&root)?;

    let mut command = Command::new(executable()?);
    command
        .current_dir(&root)
        .env_clear()
        .env("LC_ALL", "C")
        .env("LANG", "C")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_SYSTEM", "/dev/null")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_OPTIONAL_LOCKS", "0")
        .env("GIT_TERMINAL_PROMPT", "0")
        .env("GIT_NO_REPLACE_OBJECTS", "1")
        .env("GIT_NO_LAZY_FETCH", "1")
        .env("GIT_ATTR_NOSYSTEM", "1")
        .arg("--no-pager");
    if !pathspec_mode.is_empty() {
        command.arg(pathspec_mode);
    }
    command
        .arg("--git-dir")
        .arg(git_dir)
        .arg("--work-tree")
        .arg(&root)
        .arg("-c")
        .arg("core.bare=false")
        .arg("-c")
        .arg(format!("core.worktree={worktree}"))
        .args([
            "-c",
            "core.fsmonitor=false",
            "-c",
            "core.untrackedCache=false",
            "-c",
            "core.trustctime=true",
            "-c",
            "core.checkStat=default",
            "-c",
            "core.ignoreStat=false",
            "-c",
            "core.autocrlf=false",
            "-c",
            "core.eol=lf",
            "-c",
            "core.safecrlf=true",
            "-c",
            "core.ignoreCase=false",
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "core.filemode=true",
            "-c",
            "core.symlinks=true",
            "-c",
            "core.sparseCheckout=false",
            "-c",
            "core.excludesFile=/dev/null",
            "-c",
            "core.attributesFile=/dev/null",
            "-c",
            "core.quotePath=true",
            "-c",
            "color.ui=false",
            "-c",
            "status.showUntrackedFiles=all",
            "-C",
        ])
        .arg(&root);
    Ok(command)
}

pub(crate) fn output(
    root: &Path,
    args: &[&str],
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<Output, String> {
    let mut command = command(root)?;
    command.args(args);
    bounded_process::output(&mut command, context, max_stream_bytes, timeout)
}

/// Run a successful bounded Git probe and return canonical UTF-8 stdout with
/// its one record-terminating newline removed. Successful stderr is rejected.
pub(crate) fn text(
    root: &Path,
    args: &[&str],
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<String, String> {
    let output = output(root, args, context, max_stream_bytes, timeout)?;
    canonical_text(output, context)
}

/// Run a command that uses only caller-supplied long-form pathspec magic.
/// This is reserved for internally constructed `:(...,literal,...)` pathspecs.
pub(crate) fn text_with_explicit_pathspec_magic(
    root: &Path,
    args: &[&str],
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<String, String> {
    let mut command = command_with_pathspec_mode(root, "--noglob-pathspecs")?;
    command.args(args);
    let output = bounded_process::output(&mut command, context, max_stream_bytes, timeout)?;
    canonical_text(output, context)
}

fn canonical_text(output: Output, context: &str) -> Result<String, String> {
    if !output.status.success() {
        let stderr = strict_text(&output.stderr, "controlled Git stderr")?;
        return Err(format!(
            "{context} exited {}{}",
            output.status,
            if stderr.is_empty() { String::new() } else { format!(": {stderr}") }
        ));
    }
    if !output.stderr.is_empty() {
        return Err(format!("{context} wrote unexpected stderr"));
    }
    let stdout = strict_text(&output.stdout, "controlled Git stdout")?;
    if stdout.is_empty() {
        return Ok(String::new());
    }
    let stdout = stdout
        .strip_suffix('\n')
        .ok_or_else(|| format!("{context} stdout did not end in a canonical newline"))?;
    Ok(stdout.to_string())
}

pub(crate) fn canonical_head(
    root: &Path,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<String, String> {
    let head = text(
        root,
        &["rev-parse", "--verify", "HEAD^{commit}"],
        context,
        max_stream_bytes,
        timeout,
    )?;
    if !is_canonical_commit(&head) {
        return Err(format!("{context} returned a non-canonical commit `{head}`"));
    }
    Ok(head)
}

pub(crate) fn status_porcelain_v1(
    root: &Path,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<Vec<String>, String> {
    let text = text(
        root,
        &["status", "--porcelain=v1", "--untracked-files=all", "--ignore-submodules=none"],
        context,
        max_stream_bytes,
        timeout,
    )?;
    if text.is_empty() {
        return Ok(Vec::new());
    }
    let lines = text.lines().map(str::to_string).collect::<Vec<_>>();
    if lines.iter().any(|line| line.len() < 3 || line.as_bytes()[2] != b' ') {
        return Err(format!("{context} returned malformed porcelain-v1 status"));
    }
    Ok(lines)
}

/// Compare every tracked worktree path with `HEAD` through a fresh temporary
/// index and isolated temporary object database. `git add --update` must
/// Git-canonicalize and hash each tracked path because the fresh index has no
/// reusable worktree stat data. The resulting index is then compared with
/// `HEAD` by blob ID and mode; newly hashed blobs never enter the repository's
/// object database. Attributes are sourced explicitly from `HEAD`, while
/// repository-local attributes and clean filters are rejected separately by
/// [`validate_status_authority`].
///
/// `excluded_relative_root` is reserved for the report producer's deliberate
/// generated-output exclusion.  All other callers must pass `None`.
pub(crate) fn tracked_content_status_porcelain_v1(
    root: &Path,
    context: &str,
    excluded_relative_root: Option<&str>,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<Vec<String>, String> {
    let root = fs::canonicalize(root)
        .map_err(|error| format!("{context} could not canonicalize worktree: {error}"))?;
    let index_before =
        current_index_status_porcelain_v1(&root, context, max_stream_bytes, timeout)?;
    if !index_before.is_empty() {
        return Ok(index_before);
    }
    let temporary =
        tempfile::Builder::new().prefix("targo-trust-content-index-").tempdir().map_err(
            |error| format!("{context} could not create a private temporary index: {error}"),
        )?;
    let temporary_index = temporary.path().join("index");
    let temporary_objects = temporary.path().join("objects");
    let temporary_object_info = temporary_objects.join("info");
    fs::create_dir(&temporary_objects).map_err(|error| {
        format!("{context} could not create an isolated temporary object database: {error}")
    })?;
    fs::create_dir(&temporary_object_info).map_err(|error| {
        format!("{context} could not create temporary object-database metadata: {error}")
    })?;

    let source_objects = canonical_object_directory(&root, context, timeout)?;
    let source_objects_text = source_objects.to_str().ok_or_else(|| {
        format!("{context} repository object directory is not a canonical UTF-8 path")
    })?;
    if source_objects_text.chars().any(|character| character.is_control()) {
        return Err(format!(
            "{context} repository object directory contains a non-canonical control character"
        ));
    }
    fs::write(temporary_object_info.join("alternates"), format!("{source_objects_text}\n"))
        .map_err(|error| format!("{context} could not bind the source object database: {error}"))?;

    let mut read_tree = command(&root)?;
    read_tree
        .env("GIT_INDEX_FILE", &temporary_index)
        .env("GIT_OBJECT_DIRECTORY", &temporary_objects)
        .arg("--attr-source=HEAD")
        .args(["read-tree", "HEAD"]);
    let initialized = bounded_process::output(
        &mut read_tree,
        &format!("{context} fresh-index initialization"),
        64 * 1024,
        timeout,
    )?;
    let initialized =
        canonical_text(initialized, &format!("{context} fresh-index initialization"))?;
    if !initialized.is_empty() {
        return Err(format!("{context} fresh-index initialization emitted unexpected output"));
    }

    let (pathspec_mode, excluded_pathspec) = match excluded_relative_root {
        Some(relative) => {
            let relative_path = Path::new(relative);
            if relative_path.as_os_str().is_empty()
                || relative_path.is_absolute()
                || relative_path
                    .components()
                    .any(|component| !matches!(component, Component::Normal(_)))
            {
                return Err(format!("{context} content exclusion path was not canonical"));
            }
            ("--noglob-pathspecs", Some(format!(":(top,literal,exclude){relative}")))
        }
        None => ("--literal-pathspecs", None),
    };
    let mut reindex = command_with_pathspec_mode(&root, pathspec_mode)?;
    reindex
        .env("GIT_INDEX_FILE", &temporary_index)
        .env("GIT_OBJECT_DIRECTORY", &temporary_objects)
        // This is a non-mutating identity calculation. Disabling safe-CRLF
        // diagnostics lets the commit-bound `text`/`eol` attributes define
        // canonical blob identity without writing a checkout or real index.
        .args(["-c", "core.safecrlf=false"])
        .arg("--attr-source=HEAD")
        .args(["add", "--update"]);
    if let Some(excluded_pathspec) = excluded_pathspec.as_deref() {
        reindex.args(["--", ".", excluded_pathspec]);
    } else {
        reindex.args(["--", "."]);
    }
    let reindexed = bounded_process::output(
        &mut reindex,
        &format!("{context} tracked-content canonical reindex"),
        64 * 1024,
        TRACKED_CONTENT_TIMEOUT,
    )?;
    let reindexed =
        canonical_text(reindexed, &format!("{context} tracked-content canonical reindex"))?;
    if !reindexed.is_empty() {
        return Err(format!("{context} tracked-content canonical reindex emitted output"));
    }

    let mut diff = command_with_pathspec_mode(&root, pathspec_mode)?;
    diff.env("GIT_INDEX_FILE", &temporary_index)
        .env("GIT_OBJECT_DIRECTORY", &temporary_objects)
        .args([
            "diff-index",
            "--cached",
            "--name-only",
            "--no-ext-diff",
            "--no-textconv",
            "--ignore-submodules=none",
            "HEAD",
        ]);
    if let Some(excluded_pathspec) = excluded_pathspec.as_deref() {
        diff.args(["--", ".", excluded_pathspec]);
    } else {
        diff.args(["--", "."]);
    }
    let content = bounded_process::output(
        &mut diff,
        &format!("{context} tracked-blob comparison"),
        max_stream_bytes,
        timeout,
    )?;
    let content = canonical_text(content, &format!("{context} tracked-blob comparison"))?;
    let content_lines = tracked_paths_to_porcelain(&content, context)?;
    if !content_lines.is_empty() {
        return Ok(content_lines);
    }

    // Close the gap between the earlier porcelain probe and worktree hashing:
    // the real index must independently still equal HEAD after the full-byte
    // comparison. The temporary index never substitutes for this assertion.
    current_index_status_porcelain_v1(&root, context, max_stream_bytes, timeout)
}

fn current_index_status_porcelain_v1(
    root: &Path,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<Vec<String>, String> {
    let content = text(
        root,
        &[
            "diff-index",
            "--cached",
            "--name-only",
            "--no-ext-diff",
            "--no-textconv",
            "--ignore-submodules=none",
            "HEAD",
            "--",
            ".",
        ],
        &format!("{context} current-index-to-HEAD comparison"),
        max_stream_bytes,
        timeout,
    )?;
    tracked_paths_to_porcelain(&content, context)
}

fn tracked_paths_to_porcelain(content: &str, context: &str) -> Result<Vec<String>, String> {
    if content.is_empty() {
        return Ok(Vec::new());
    }
    let mut lines = Vec::new();
    for path in content.lines() {
        if path.is_empty() || path.len() > MAX_INDEX_RECORD_BYTES {
            return Err(format!("{context} tracked-content comparison returned a malformed path"));
        }
        if lines.len() >= MAX_INDEX_ENTRIES {
            return Err(format!(
                "{context} tracked-content comparison contains more than {MAX_INDEX_ENTRIES} entries"
            ));
        }
        lines.push(format!(" M {path}"));
    }
    Ok(lines)
}

fn canonical_object_directory(
    root: &Path,
    context: &str,
    timeout: Duration,
) -> Result<PathBuf, String> {
    let common_dir = text(
        root,
        &["rev-parse", "--git-common-dir"],
        &format!("{context} Git common-directory probe"),
        64 * 1024,
        timeout,
    )?;
    let common_dir = Path::new(&common_dir);
    let common_dir =
        if common_dir.is_absolute() { common_dir.to_path_buf() } else { root.join(common_dir) };
    let objects = fs::canonicalize(common_dir.join("objects")).map_err(|error| {
        format!("{context} could not canonicalize the repository object directory: {error}")
    })?;
    if !objects.is_dir() {
        return Err(format!("{context} repository object directory is not a directory"));
    }
    Ok(objects)
}

/// Reject repository-local mechanisms that can make a cleanliness probe omit
/// material paths. Tracked `.gitignore` files remain commit-bound authority.
pub(crate) fn validate_status_authority(
    root: &Path,
    context: &str,
    _caller_max_stream_bytes: usize,
    timeout: Duration,
) -> Result<(), String> {
    require_no_local_excludes(root, context, timeout)?;
    require_no_local_attributes(root, context, timeout)?;
    reject_effective_filter_authority(root, context, timeout)?;
    let hidden_ignore_files = text_with_explicit_pathspec_magic(
        root,
        &[
            "ls-files",
            "--others",
            "--ignored",
            "--exclude-standard",
            "--",
            ":(icase,glob)**/.gitignore",
            ":(icase,glob)**/.gitattributes",
        ],
        &format!("{context} untracked-ignore-authority probe"),
        MAX_INDEX_INVENTORY_BYTES,
        timeout,
    )?;
    if !hidden_ignore_files.is_empty() {
        validate_inventory_lines(&hidden_ignore_files, context, "untracked ignore/attribute")?;
        return Err(format!(
            "{context} rejected untracked .gitignore authority or untracked .gitattributes authority hidden by ignore rules"
        ));
    }
    let entries = text(
        root,
        &["ls-files", "-v"],
        &format!("{context} index-visibility probe"),
        MAX_INDEX_INVENTORY_BYTES,
        timeout,
    )?;
    let mut entry_count = 0usize;
    for line in entries.lines() {
        entry_count = entry_count
            .checked_add(1)
            .ok_or_else(|| format!("{context} index entry count overflowed"))?;
        if entry_count > MAX_INDEX_ENTRIES {
            return Err(format!("{context} index contains more than {MAX_INDEX_ENTRIES} entries"));
        }
        if line.len() > MAX_INDEX_RECORD_BYTES {
            return Err(format!(
                "{context} index contains a path record longer than {MAX_INDEX_RECORD_BYTES} bytes"
            ));
        }
        if !line.starts_with("H ") {
            return Err(format!(
                "{context} rejected skip-worktree, assume-unchanged, unmerged, or hidden index entries"
            ));
        }
    }
    Ok(())
}

fn validate_inventory_lines(value: &str, context: &str, inventory: &str) -> Result<(), String> {
    let mut entry_count = 0usize;
    for line in value.lines() {
        entry_count = entry_count
            .checked_add(1)
            .ok_or_else(|| format!("{context} {inventory} entry count overflowed"))?;
        if entry_count > MAX_INDEX_ENTRIES {
            return Err(format!(
                "{context} {inventory} inventory contains more than {MAX_INDEX_ENTRIES} entries"
            ));
        }
        if line.len() > MAX_INDEX_RECORD_BYTES {
            return Err(format!(
                "{context} {inventory} path record is longer than {MAX_INDEX_RECORD_BYTES} bytes"
            ));
        }
    }
    Ok(())
}

pub(crate) fn exact_status_porcelain_v1(
    root: &Path,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<Vec<String>, String> {
    let mut visited = BTreeSet::new();
    exact_status_recursive(root, context, max_stream_bytes, timeout, &mut visited, true)
}

fn exact_status_recursive(
    root: &Path,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
    visited: &mut BTreeSet<PathBuf>,
    top_level: bool,
) -> Result<Vec<String>, String> {
    let root = fs::canonicalize(root)
        .map_err(|error| format!("{context} could not canonicalize worktree: {error}"))?;
    if !visited.insert(root.clone()) {
        return Err(format!(
            "{context} encountered a repeated or cyclic submodule worktree {}",
            root.display()
        ));
    }
    if visited.len() > MAX_RECURSIVE_WORKTREES {
        return Err(format!(
            "{context} exceeded the {MAX_RECURSIVE_WORKTREES}-worktree recursion bound"
        ));
    }

    validate_status_authority(&root, context, max_stream_bytes, timeout)?;
    // Porcelain is authoritative only for untracked paths. Its tracked `M`
    // rows are stat-driven diagnostics and can be false positives for bytes
    // that commit-bound attributes canonicalize to the exact HEAD blob.
    // Staged state and tracked worktree state are proven independently below.
    let untracked_lines = status_porcelain_v1(&root, context, max_stream_bytes, timeout)?
        .into_iter()
        .filter(|line| line.starts_with("?? "))
        .collect::<Vec<_>>();
    if !untracked_lines.is_empty() {
        if top_level {
            return Ok(untracked_lines);
        }
        return Err(format!(
            "{context} submodule {} has {} untracked status entries",
            root.display(),
            untracked_lines.len()
        ));
    }

    let lines =
        tracked_content_status_porcelain_v1(&root, context, None, max_stream_bytes, timeout)?;
    if !lines.is_empty() {
        if top_level {
            return Ok(lines);
        }
        return Err(format!(
            "{context} submodule {} has {} content-authoritative tracked changes",
            root.display(),
            lines.len()
        ));
    }

    validate_submodules_recursive(&root, context, max_stream_bytes, timeout, visited)?;
    Ok(lines)
}

/// Validate every initialized gitlink recursively while allowing the caller to
/// handle a deliberate top-level output exclusion separately.
pub(crate) fn require_clean_submodules(
    root: &Path,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<(), String> {
    let root = fs::canonicalize(root)
        .map_err(|error| format!("{context} could not canonicalize worktree: {error}"))?;
    let mut visited = BTreeSet::from([root.clone()]);
    validate_submodules_recursive(&root, context, max_stream_bytes, timeout, &mut visited)
}

fn validate_submodules_recursive(
    root: &Path,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
    visited: &mut BTreeSet<PathBuf>,
) -> Result<(), String> {
    for relative in gitlink_paths(root, context, timeout)? {
        let mut candidate = root.to_path_buf();
        for component in relative.components() {
            let Component::Normal(name) = component else {
                return Err(format!("{context} submodule path was not canonical"));
            };
            candidate.push(name);
            let metadata = fs::symlink_metadata(&candidate).map_err(|error| {
                format!(
                    "{context} requires initialized submodule path {}: {error}",
                    candidate.display()
                )
            })?;
            if metadata.file_type().is_symlink() || !metadata.is_dir() {
                return Err(format!(
                    "{context} submodule path is not an exact directory: {}",
                    candidate.display()
                ));
            }
        }
        let submodule = fs::canonicalize(&candidate).map_err(|error| {
            format!("{context} could not canonicalize submodule {}: {error}", candidate.display())
        })?;
        if submodule.parent().is_none() || !submodule.starts_with(&root) {
            return Err(format!(
                "{context} submodule escapes its parent worktree: {}",
                submodule.display()
            ));
        }
        exact_status_recursive(&submodule, context, max_stream_bytes, timeout, visited, false)?;
    }
    Ok(())
}

fn gitlink_paths(root: &Path, context: &str, timeout: Duration) -> Result<Vec<PathBuf>, String> {
    let output = output(
        root,
        &["ls-files", "--stage", "-z"],
        &format!("{context} gitlink inventory"),
        MAX_INDEX_INVENTORY_BYTES,
        timeout,
    )?;
    if !output.status.success() || !output.stderr.is_empty() {
        return Err(format!("{context} could not inventory Git index gitlinks"));
    }
    if output.stdout.is_empty() {
        return Ok(Vec::new());
    }
    if !output.stdout.ends_with(&[0]) {
        return Err(format!("{context} Git index inventory lacked a terminal NUL"));
    }
    let mut gitlinks = Vec::new();
    let mut entry_count = 0usize;
    for record in output.stdout[..output.stdout.len() - 1].split(|byte| *byte == 0) {
        entry_count = entry_count
            .checked_add(1)
            .ok_or_else(|| format!("{context} Git index entry count overflowed"))?;
        if entry_count > MAX_INDEX_ENTRIES {
            return Err(format!(
                "{context} Git index contains more than {MAX_INDEX_ENTRIES} entries"
            ));
        }
        if record.len() > MAX_INDEX_RECORD_BYTES {
            return Err(format!(
                "{context} Git index contains a record longer than {MAX_INDEX_RECORD_BYTES} bytes"
            ));
        }
        let Some(tab) = record.iter().position(|byte| *byte == b'\t') else {
            return Err(format!("{context} Git index inventory record was malformed"));
        };
        let metadata = std::str::from_utf8(&record[..tab])
            .map_err(|_| format!("{context} Git index metadata was not UTF-8"))?;
        let fields = metadata.split(' ').collect::<Vec<_>>();
        if fields.len() != 3 || fields[2] != "0" || !is_canonical_commit(fields[1]) {
            return Err(format!("{context} Git index contains an unmerged or malformed entry"));
        }
        if fields[0] != "160000" {
            continue;
        }
        let path = std::str::from_utf8(&record[tab + 1..])
            .map_err(|_| format!("{context} submodule path was not UTF-8"))?;
        let path = Path::new(path);
        if path.as_os_str().is_empty()
            || path.is_absolute()
            || path.components().any(|component| !matches!(component, Component::Normal(_)))
        {
            return Err(format!("{context} submodule path was not canonical"));
        }
        gitlinks.push(path.to_path_buf());
        if gitlinks.len() >= MAX_RECURSIVE_WORKTREES {
            return Err(format!(
                "{context} Git index contains too many gitlinks for the {MAX_RECURSIVE_WORKTREES}-worktree recursion bound"
            ));
        }
    }
    gitlinks.sort();
    if gitlinks.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(format!("{context} Git index contains duplicate gitlinks"));
    }
    Ok(gitlinks)
}

fn require_no_local_excludes(root: &Path, context: &str, timeout: Duration) -> Result<(), String> {
    let path = text(
        root,
        &["rev-parse", "--git-path", "info/exclude"],
        &format!("{context} local-exclude path probe"),
        64 * 1024,
        timeout,
    )?;
    let path = if Path::new(&path).is_absolute() { PathBuf::from(path) } else { root.join(path) };
    let metadata = match fs::symlink_metadata(&path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => {
            return Err(format!(
                "{context} could not inspect local excludes {}: {error}",
                path.display()
            ));
        }
    };
    if metadata.file_type().is_symlink()
        || !metadata.file_type().is_file()
        || metadata.len() > MAX_LOCAL_EXCLUDE_BYTES
    {
        return Err(format!(
            "{context} local Git info/exclude is not a bounded exact regular file"
        ));
    }
    let contents = fs::read_to_string(&path).map_err(|error| {
        format!("{context} could not read local excludes {}: {error}", path.display())
    })?;
    if contents.lines().any(|line| !line.trim().is_empty() && !line.starts_with('#')) {
        return Err(format!(
            "{context} local Git info/exclude contains material rules; only commit-bound ignore authority is accepted"
        ));
    }
    Ok(())
}

fn require_no_local_attributes(
    root: &Path,
    context: &str,
    timeout: Duration,
) -> Result<(), String> {
    let path = text(
        root,
        &["rev-parse", "--git-path", "info/attributes"],
        &format!("{context} local-attributes path probe"),
        64 * 1024,
        timeout,
    )?;
    let path = if Path::new(&path).is_absolute() { PathBuf::from(path) } else { root.join(path) };
    let metadata = match fs::symlink_metadata(&path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => {
            return Err(format!(
                "{context} could not inspect local attributes {}: {error}",
                path.display()
            ));
        }
    };
    if metadata.file_type().is_symlink()
        || !metadata.file_type().is_file()
        || metadata.len() > MAX_LOCAL_EXCLUDE_BYTES
    {
        return Err(format!(
            "{context} local Git info/attributes is not a bounded exact regular file"
        ));
    }
    let contents = fs::read_to_string(&path).map_err(|error| {
        format!("{context} could not read local attributes {}: {error}", path.display())
    })?;
    if contents.lines().any(|line| !line.trim().is_empty() && !line.starts_with('#')) {
        return Err(format!(
            "{context} local Git info/attributes contains material rules; only commit-bound attribute authority is accepted"
        ));
    }
    Ok(())
}

fn reject_effective_filter_authority(
    root: &Path,
    context: &str,
    timeout: Duration,
) -> Result<(), String> {
    let output = output(
        root,
        &["config", "--includes", "--name-only", "--null", "--list"],
        &format!("{context} effective filter configuration probe"),
        MAX_CONFIG_INVENTORY_BYTES,
        timeout,
    )?;
    if !output.status.success() || !output.stderr.is_empty() {
        return Err(format!("{context} could not inspect effective Git filter configuration"));
    }
    if !output.stdout.is_empty() && !output.stdout.ends_with(&[0]) {
        return Err(format!("{context} Git configuration inventory lacked a terminal NUL"));
    }
    for raw_name in output.stdout.split(|byte| *byte == 0).filter(|name| !name.is_empty()) {
        let name = std::str::from_utf8(raw_name)
            .map_err(|_| format!("{context} Git configuration name was not UTF-8"))?
            .to_ascii_lowercase();
        if name.starts_with("filter.")
            && (name.ends_with(".clean")
                || name.ends_with(".process")
                || name.ends_with(".required"))
        {
            return Err(format!(
                "{context} rejected effective Git clean/process filter authority `{name}`"
            ));
        }
    }
    Ok(())
}

fn valid_git_marker(root: &Path) -> Result<bool, String> {
    let marker = root.join(".git");
    let metadata = match fs::symlink_metadata(&marker) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(false),
        Err(error) => {
            return Err(format!("could not inspect Git marker {}: {error}", marker.display()));
        }
    };
    if metadata.file_type().is_symlink() {
        return Err(format!("Git marker must not be a symlink: {}", marker.display()));
    }
    if !metadata.is_dir() && !metadata.is_file() {
        return Err(format!("Git marker is not a directory or regular file: {}", marker.display()));
    }
    Ok(true)
}

fn resolve_git_dir(root: &Path) -> Result<PathBuf, String> {
    let marker = root.join(".git");
    let metadata = fs::symlink_metadata(&marker)
        .map_err(|error| format!("could not inspect Git marker {}: {error}", marker.display()))?;
    let git_dir = if metadata.is_dir() {
        fs::canonicalize(&marker).map_err(|error| {
            format!("could not canonicalize Git directory {}: {error}", marker.display())
        })?
    } else {
        if !metadata.is_file() || metadata.len() > 4096 {
            return Err(format!(
                "Git marker is not a bounded regular gitdir file: {}",
                marker.display()
            ));
        }
        let record = fs::read_to_string(&marker)
            .map_err(|error| format!("could not read Git marker {}: {error}", marker.display()))?;
        let value = record
            .strip_suffix('\n')
            .and_then(|record| record.strip_prefix("gitdir: "))
            .filter(|value| !value.is_empty() && !value.contains(['\n', '\r']))
            .ok_or_else(|| {
                format!("Git marker is not one canonical gitdir record: {}", marker.display())
            })?;
        let value = Path::new(value);
        let candidate = if value.is_absolute() { value.to_path_buf() } else { root.join(value) };
        fs::canonicalize(&candidate).map_err(|error| {
            format!(
                "could not canonicalize linked-worktree Git directory {}: {error}",
                candidate.display()
            )
        })?
    };
    if !git_dir.is_dir() {
        return Err(format!("controlled Git directory is not a directory: {}", git_dir.display()));
    }
    Ok(git_dir)
}

fn strict_text<'a>(bytes: &'a [u8], context: &str) -> Result<&'a str, String> {
    let value = std::str::from_utf8(bytes)
        .map_err(|error| format!("{context} was not valid UTF-8: {error}"))?;
    if value.chars().any(|character| character.is_control() && !matches!(character, '\n' | '\t')) {
        return Err(format!("{context} contained a non-canonical control character"));
    }
    Ok(value)
}

fn is_canonical_commit(value: &str) -> bool {
    value.len() == 40
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::fs::MetadataExt;
    use std::os::unix::fs::PermissionsExt;

    fn fixture_repo(prefix: &str) -> tempfile::TempDir {
        let directory = tempfile::Builder::new().prefix(prefix).tempdir().expect("temp repo");
        let git = executable().expect("controlled Git executable");
        let mut init = Command::new(&git);
        init.env_clear().env("LC_ALL", "C").args(["init", "--quiet"]).arg(directory.path());
        assert!(init.status().expect("run git init").success());
        fs::write(directory.path().join("tracked.txt"), "fixture\n").expect("write fixture");

        let mut add = Command::new(&git);
        add.env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(directory.path())
            .args(["add", "tracked.txt"]);
        assert!(add.status().expect("run git add").success());

        let mut commit = Command::new(git);
        commit.env_clear().env("LC_ALL", "C").arg("-C").arg(directory.path()).args([
            "-c",
            "user.name=Trust Tests",
            "-c",
            "user.email=trust-tests@example.invalid",
            "commit",
            "--quiet",
            "-m",
            "fixture",
        ]);
        assert!(commit.status().expect("run git commit").success());
        directory
    }

    #[test]
    fn fixed_git_ignores_a_fake_path_executable() {
        let repository = fixture_repo("controlled-git-path-");
        let fake = tempfile::Builder::new().prefix("controlled-git-fake-").tempdir().unwrap();
        let marker = fake.path().join("invoked");
        let fake_git = fake.path().join("git");
        fs::write(&fake_git, format!("#!/bin/sh\n: > '{}'\nexit 99\n", marker.display()))
            .expect("write fake git");
        fs::set_permissions(&fake_git, fs::Permissions::from_mode(0o755)).unwrap();

        let mut command = command(repository.path()).expect("controlled command");
        command.env("PATH", fake.path()).args(["rev-parse", "--verify", "HEAD^{commit}"]);
        let output = bounded_process::output(
            &mut command,
            "fake-PATH controlled Git regression",
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect("run controlled Git");
        assert!(output.status.success());
        assert!(!marker.exists(), "PATH-resolved fake Git executed");
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn macos_executes_real_git_instead_of_the_xcselect_tool_shim() {
        let git = executable().expect("controlled real Git executable");
        let shim = fs::canonicalize("/usr/bin/git").expect("canonical Apple Git tool shim");
        assert_ne!(git, shim, "controlled Git selected the basename-sensitive xcselect shim");
        assert!(
            SYSTEM_GIT_CANDIDATES.iter().any(|candidate| {
                fs::canonicalize(candidate)
                    .ok()
                    .as_deref()
                    .is_some_and(|candidate| candidate == git.as_path())
            }),
            "controlled Git escaped its fixed real-binary candidates: {}",
            git.display()
        );

        let output = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("--version")
            .output()
            .expect("run controlled real Git directly");
        assert!(output.status.success());
        assert!(output.stdout.starts_with(b"git version "));
    }

    #[test]
    fn selected_git_has_a_root_owned_immutable_canonical_chain() {
        let git = executable().expect("controlled Git executable");
        let parent = git.parent().expect("controlled Git parent");
        validate_root_owned_immutable_directory_chain(parent, "test canonical")
            .expect("selected Git ancestor chain is immutable authority");
        let metadata = fs::symlink_metadata(&git).expect("selected Git metadata");
        validate_root_owned_executable(&metadata, &git, "test canonical")
            .expect("selected Git leaf is immutable authority");
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn macos_accepts_immutable_clt_and_rejects_a_mutable_applications_chain() {
        let clt = Path::new("/Library/Developer/CommandLineTools/usr/bin/git");
        if clt.exists() {
            assert_eq!(
                trusted_system_executable(clt).expect("immutable CLT Git is accepted"),
                fs::canonicalize(clt).expect("canonical CLT Git")
            );
        }

        let applications = Path::new("/Applications");
        let metadata = fs::symlink_metadata(applications).expect("/Applications metadata");
        if metadata.permissions().mode() & 0o022 != 0 {
            let xcode = Path::new("/Applications/Xcode.app/Contents/Developer/usr/bin/git");
            let error = trusted_system_executable(xcode)
                .expect_err("group-writable /Applications cannot be Git authority");
            assert!(
                error.contains("/Applications"),
                "rejection names the mutable ancestor: {error}"
            );
        }
    }

    #[test]
    fn caller_status_limit_does_not_bound_index_authority_inventories() {
        let repository = fixture_repo("controlled-git-inventory-cap-");
        let raw_inventory = output(
            repository.path(),
            &["ls-files", "--stage", "-z"],
            "inventory-cap fixture probe",
            MAX_INDEX_INVENTORY_BYTES,
            Duration::from_secs(30),
        )
        .expect("read fixture index inventory");
        assert!(raw_inventory.stdout.len() > 1, "fixture inventory must exceed the caller limit");

        let status = exact_status_porcelain_v1(
            repository.path(),
            "independent inventory cap regression",
            1,
            Duration::from_secs(30),
        )
        .expect("a clean repository must fit a one-byte status-output budget");
        assert!(status.is_empty());
    }

    #[test]
    fn repo_local_fsmonitor_and_worktree_config_cannot_affect_status() {
        let repository = fixture_repo("controlled-git-fsmonitor-");
        let marker = repository.path().join("fsmonitor-invoked");
        let monitor = repository.path().join("malicious-fsmonitor");
        fs::write(&monitor, format!("#!/bin/sh\n: > '{}'\nprintf '0\\n'\n", marker.display()))
            .expect("write fsmonitor");
        fs::set_permissions(&monitor, fs::Permissions::from_mode(0o755)).unwrap();

        let git = executable().expect("controlled Git executable");
        for (key, value) in [
            ("core.fsmonitor", monitor.to_str().unwrap()),
            ("core.worktree", "/definitely/not/the/repository"),
        ] {
            let status = Command::new(&git)
                .env_clear()
                .env("LC_ALL", "C")
                .arg("-C")
                .arg(repository.path())
                .args(["config", "--local", key, value])
                .status()
                .expect("write local Git config");
            assert!(status.success());
        }

        let lines = status_porcelain_v1(
            repository.path(),
            "repository-local config regression",
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect("controlled status");
        assert!(lines.iter().any(|line| line.ends_with("malicious-fsmonitor")));
        assert!(!marker.exists(), "repository-local fsmonitor executed");
    }

    #[test]
    fn hidden_untracked_gitignore_cannot_make_a_dirty_tree_look_clean() {
        let repository = fixture_repo("controlled-git-hidden-ignore-");
        fs::write(repository.path().join(".gitignore"), "*\n").expect("write hidden ignore");
        fs::write(repository.path().join("hidden.txt"), "hidden\n").expect("write hidden file");

        let error = exact_status_porcelain_v1(
            repository.path(),
            "hidden ignore regression",
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect_err("untracked ignore authority must fail closed");
        assert!(error.contains("untracked .gitignore authority"));
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn case_folded_hidden_untracked_gitignore_is_rejected() {
        let repository = fixture_repo("controlled-git-hidden-ignore-case-");
        fs::write(repository.path().join(".GITIGNORE"), "*\n").expect("write hidden ignore");
        fs::write(repository.path().join("hidden.txt"), "hidden\n").expect("write hidden file");

        let error = exact_status_porcelain_v1(
            repository.path(),
            "case-folded hidden ignore regression",
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect_err("case-folded untracked ignore authority must fail closed");
        assert!(error.contains("untracked .gitignore authority"));
    }

    #[test]
    fn whitespace_prefixed_local_exclude_is_material_authority() {
        let repository = fixture_repo("controlled-git-local-exclude-");
        fs::write(repository.path().join(".git/info/exclude"), " #secret\n")
            .expect("write material local exclude");
        fs::write(repository.path().join(" #secret"), "hidden\n").expect("write hidden file");

        let error = exact_status_porcelain_v1(
            repository.path(),
            "local exclude regression",
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect_err("material local exclude must fail closed");
        assert!(error.contains("info/exclude contains material rules"));
    }

    #[test]
    fn local_and_hidden_untracked_attributes_are_rejected() {
        let local = fixture_repo("controlled-git-local-attributes-");
        fs::write(local.path().join(".git/info/attributes"), " * filter=evil\n")
            .expect("write material local attributes");
        let error = exact_status_porcelain_v1(
            local.path(),
            "local attributes regression",
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect_err("material local attributes must fail closed");
        assert!(error.contains("info/attributes contains material rules"));

        let hidden = fixture_repo("controlled-git-hidden-attributes-");
        fs::write(hidden.path().join(".gitignore"), ".gitattributes\n")
            .expect("write tracked ignore policy");
        let mut add = command(hidden.path()).expect("controlled Git");
        add.args(["add", ".gitignore"]);
        assert!(add.status().expect("add ignore policy").success());
        let git = executable().expect("controlled Git executable");
        let committed = Command::new(git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(hidden.path())
            .args([
                "-c",
                "user.name=Trust Tests",
                "-c",
                "user.email=trust-tests@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "ignore attributes fixture",
            ])
            .status()
            .expect("commit ignore policy");
        assert!(committed.success());
        fs::write(hidden.path().join(".gitattributes"), "* filter=evil\n")
            .expect("write hidden attributes");
        let error = exact_status_porcelain_v1(
            hidden.path(),
            "hidden attributes regression",
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect_err("hidden untracked attributes must fail closed");
        assert!(error.contains("untracked .gitattributes authority"));
    }

    #[test]
    fn effective_clean_filter_is_rejected_without_execution() {
        let repository = fixture_repo("controlled-git-filter-");
        let marker = repository.path().join("filter-invoked");
        let filter = repository.path().join("evil-filter");
        fs::write(&filter, format!("#!/bin/sh\n: > '{}'\ncat\n", marker.display()))
            .expect("write filter fixture");
        fs::set_permissions(&filter, fs::Permissions::from_mode(0o755)).unwrap();
        let git = executable().expect("controlled Git executable");
        let configured = Command::new(git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(repository.path())
            .args(["config", "--local", "filter.evil.clean"])
            .arg(&filter)
            .status()
            .expect("configure filter fixture");
        assert!(configured.success());

        let error = exact_status_porcelain_v1(
            repository.path(),
            "filter authority regression",
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect_err("effective clean filter must fail closed");
        assert!(error.contains("clean/process filter authority"));
        assert!(!marker.exists(), "rejected clean filter executed");
    }

    #[test]
    fn explicit_literal_exclusion_magic_is_not_disabled() {
        let repository = fixture_repo("controlled-git-exclude-");
        let output_dir = repository.path().join("reports/generated");
        fs::create_dir_all(&output_dir).expect("create output directory");
        fs::write(output_dir.join("result.json"), "{}\n").expect("write generated output");

        let git = executable().expect("controlled Git executable");
        let added = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(repository.path())
            .args(["add", "reports/generated/result.json"])
            .status()
            .expect("add generated output fixture");
        assert!(added.success());
        let committed = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(repository.path())
            .args([
                "-c",
                "user.name=Trust Tests",
                "-c",
                "user.email=trust-tests@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "generated output fixture",
            ])
            .status()
            .expect("commit generated output fixture");
        assert!(committed.success());
        fs::write(output_dir.join("result.json"), "{\"changed\":true}\n")
            .expect("modify generated output fixture");

        let status = text_with_explicit_pathspec_magic(
            repository.path(),
            &[
                "status",
                "--porcelain=v1",
                "--untracked-files=all",
                "--ignore-submodules=none",
                "--",
                ".",
                ":(top,literal,exclude)reports/generated",
            ],
            "explicit exclusion regression",
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect("controlled status with explicit exclusion");
        assert!(status.is_empty());

        let without_exclusion = tracked_content_status_porcelain_v1(
            repository.path(),
            "content exclusion control regression",
            None,
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect("content-authoritative status without exclusion");
        assert!(
            without_exclusion.iter().any(|line| line.ends_with("reports/generated/result.json"))
        );
        let with_exclusion = tracked_content_status_porcelain_v1(
            repository.path(),
            "content exclusion regression",
            Some("reports/generated"),
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect("content-authoritative status with explicit exclusion");
        assert!(with_exclusion.is_empty());
    }

    #[test]
    fn tracked_content_comparison_respects_commit_bound_text_attributes() {
        let repository = fixture_repo("controlled-git-attributes-content-");
        fs::write(repository.path().join(".gitattributes"), "tracked.txt text\n")
            .expect("write committed attributes fixture");
        let git = executable().expect("controlled Git executable");
        let added = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(repository.path())
            .args(["add", ".gitattributes"])
            .status()
            .expect("add committed attributes fixture");
        assert!(added.success());
        let committed = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(repository.path())
            .args([
                "-c",
                "user.name=Trust Tests",
                "-c",
                "user.email=trust-tests@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "committed attributes fixture",
            ])
            .status()
            .expect("commit attributes fixture");
        assert!(committed.success());

        fs::write(repository.path().join("tracked.txt"), "fixture\r\n")
            .expect("write canonically equivalent CRLF content");
        let _diagnostic_status = status_porcelain_v1(
            repository.path(),
            "commit-bound text attributes diagnostic",
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect("ordinary diagnostic status");
        let authoritative = tracked_content_status_porcelain_v1(
            repository.path(),
            "commit-bound text attributes authoritative comparison",
            None,
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect("content-authoritative comparison with committed attributes");
        assert!(
            authoritative.is_empty(),
            "canonical re-index ignored committed text normalization: {authoritative:?}"
        );
        let lines = exact_status_porcelain_v1(
            repository.path(),
            "commit-bound text attributes regression",
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect("content-authoritative status with committed attributes");
        assert!(lines.is_empty(), "committed text normalization was not respected: {lines:?}");
    }

    #[test]
    fn tracked_content_reindex_covers_file_type_and_executable_mode() {
        use std::os::unix::fs::symlink;

        let repository = fixture_repo("controlled-git-type-mode-");
        let script_path = repository.path().join("executable.sh");
        fs::write(&script_path, "#!/bin/sh\nexit 0\n").expect("write executable fixture");
        let git = executable().expect("controlled Git executable");
        let added = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(repository.path())
            .args(["add", "executable.sh"])
            .status()
            .expect("add mode fixture");
        assert!(added.success());
        let committed = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(repository.path())
            .args([
                "-c",
                "user.name=Trust Tests",
                "-c",
                "user.email=trust-tests@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "type and mode fixture",
            ])
            .status()
            .expect("commit mode fixture");
        assert!(committed.success());

        fs::remove_file(repository.path().join("tracked.txt")).expect("remove regular fixture");
        symlink("replacement-target", repository.path().join("tracked.txt"))
            .expect("replace regular fixture with symlink");
        let mut permissions =
            fs::metadata(&script_path).expect("executable metadata").permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&script_path, permissions).expect("make fixture executable");

        let lines = tracked_content_status_porcelain_v1(
            repository.path(),
            "tracked type/mode regression",
            None,
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect("content-authoritative type/mode status");
        assert!(lines.iter().any(|line| line.ends_with("tracked.txt")));
        assert!(lines.iter().any(|line| line.ends_with("executable.sh")));
    }

    #[test]
    fn tracked_content_pass_independently_rejects_matching_index_and_worktree_changes() {
        let repository = fixture_repo("controlled-git-index-worktree-");
        fs::write(repository.path().join("tracked.txt"), "changed\n")
            .expect("write matching index/worktree change");
        let git = executable().expect("controlled Git executable");
        let staged = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(repository.path())
            .args(["add", "tracked.txt"])
            .status()
            .expect("stage matching index/worktree change");
        assert!(staged.success());

        let lines = tracked_content_status_porcelain_v1(
            repository.path(),
            "independent real-index regression",
            None,
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect("content-authoritative real-index status");
        assert!(lines.iter().any(|line| line.ends_with("tracked.txt")));
    }

    #[test]
    fn local_minimal_stat_config_cannot_hide_same_size_content_replacement() {
        let repository = fixture_repo("controlled-git-stat-");
        let tracked = repository.path().join("tracked.txt");
        let git = executable().expect("controlled Git executable");
        let path = CString::new(tracked.as_os_str().as_bytes()).expect("C path");
        let old_timestamps = [
            libc::timespec { tv_sec: 1_600_000_000, tv_nsec: 0 },
            libc::timespec { tv_sec: 1_600_000_000, tv_nsec: 0 },
        ];
        // SAFETY: `path` is NUL-terminated and `old_timestamps` contains the
        // two values required by utimensat.
        let result =
            unsafe { libc::utimensat(libc::AT_FDCWD, path.as_ptr(), old_timestamps.as_ptr(), 0) };
        assert_eq!(result, 0, "set non-racy tracked-file timestamps");
        let refreshed = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(repository.path())
            .args(["update-index", "--refresh"])
            .status()
            .expect("refresh fixture index stat data");
        assert!(refreshed.success());
        let original = fs::metadata(&tracked).expect("tracked metadata");
        for (key, value) in [("core.trustctime", "false"), ("core.checkStat", "minimal")] {
            let status = Command::new(&git)
                .env_clear()
                .env("LC_ALL", "C")
                .arg("-C")
                .arg(repository.path())
                .args(["config", "--local", key, value])
                .status()
                .expect("write local stat config");
            assert!(status.success());
        }

        fs::write(&tracked, "changed\n").expect("replace tracked bytes with same length");
        let timestamps = [
            libc::timespec { tv_sec: original.atime(), tv_nsec: original.atime_nsec() },
            libc::timespec { tv_sec: original.mtime(), tv_nsec: original.mtime_nsec() },
        ];
        // SAFETY: `path` is NUL-terminated and `timestamps` contains exactly
        // the two timespec values required by utimensat.
        let result =
            unsafe { libc::utimensat(libc::AT_FDCWD, path.as_ptr(), timestamps.as_ptr(), 0) };
        assert_eq!(result, 0, "restore tracked-file timestamps");

        let raw = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(repository.path())
            .args(["status", "--porcelain=v1"])
            .output()
            .expect("run locally configured Git status");
        assert!(raw.status.success());
        assert!(raw.stdout.is_empty(), "fixture did not reproduce the local-config bypass");

        let lines = exact_status_porcelain_v1(
            repository.path(),
            "stat authority regression",
            64 * 1024,
            Duration::from_secs(30),
        )
        .expect("controlled status");
        assert!(lines.iter().any(|line| line.ends_with("tracked.txt")));
    }

    #[test]
    fn hidden_untracked_content_inside_gitlink_cannot_look_recursively_clean() {
        let repository = fixture_repo("controlled-git-submodule-");
        let nested = repository.path().join("nested");
        let git = executable().expect("controlled Git executable");

        let initialized = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .args(["init", "--quiet"])
            .arg(&nested)
            .status()
            .expect("initialize nested repository");
        assert!(initialized.success());
        fs::write(nested.join("tracked.txt"), "nested\n").expect("write nested fixture");
        let added = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(&nested)
            .args(["add", "tracked.txt"])
            .status()
            .expect("add nested fixture");
        assert!(added.success());
        let committed = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(&nested)
            .args([
                "-c",
                "user.name=Trust Tests",
                "-c",
                "user.email=trust-tests@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "nested fixture",
            ])
            .status()
            .expect("commit nested fixture");
        assert!(committed.success());
        let nested_head = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(&nested)
            .args(["rev-parse", "--verify", "HEAD^{commit}"])
            .output()
            .expect("read nested HEAD");
        assert!(nested_head.status.success());
        let nested_head = String::from_utf8(nested_head.stdout).expect("nested HEAD UTF-8");
        let cache_info = format!("160000,{},nested", nested_head.trim());
        let staged = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(repository.path())
            .args(["update-index", "--add", "--cacheinfo"])
            .arg(&cache_info)
            .status()
            .expect("stage gitlink");
        assert!(staged.success());
        let parent_commit = Command::new(&git)
            .env_clear()
            .env("LC_ALL", "C")
            .arg("-C")
            .arg(repository.path())
            .args([
                "-c",
                "user.name=Trust Tests",
                "-c",
                "user.email=trust-tests@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "gitlink fixture",
            ])
            .status()
            .expect("commit gitlink fixture");
        assert!(parent_commit.success());

        fs::write(nested.join(".gitignore"), "*\n").expect("write nested hidden ignore");
        fs::write(nested.join("hidden.txt"), "hidden\n").expect("write nested hidden file");
        match exact_status_porcelain_v1(
            repository.path(),
            "recursive submodule regression",
            64 * 1024,
            Duration::from_secs(30),
        ) {
            Ok(lines) => assert!(!lines.is_empty(), "nested hidden content looked clean"),
            Err(error) => assert!(
                error.contains("untracked .gitignore authority")
                    || error.contains("submodule")
                    || error.contains("gitlink")
            ),
        }
    }
}
