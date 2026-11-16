//! Trust: durable execution facts for the bounded native repository check.
//!
//! This stores inner bootstrap execution facts, never a proof verdict or a claim
//! about the outer command's process cleanup. Repository snapshots do not cover
//! arbitrary test/build-script reads, so production callers must execute again.
//! The caller owns the ordinary bootstrap lock; a second, nonblocking lease
//! protects this transaction itself. Reuse is exercised only by controlled tests.

use std::collections::BTreeSet;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use serde_derive::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::utils::helpers::hex_encode;

mod outputs;
pub(crate) use outputs::{InputSnapshot, OutputNamespace, RepositorySnapshot};

const SCHEMA: &str = "trust.native-repo-execution/v2";
const AUTHORITY: &str = "completed inner bootstrap compiler check and UI test; no proof claim";

/// Production has no policy that asserts a complete read closure.
pub(crate) enum ReusePolicy {
    RecordOnly,
    #[cfg(test)]
    ControlledFixture,
}

impl ReusePolicy {
    fn permits_reuse(self) -> bool {
        match self {
            Self::RecordOnly => false,
            #[cfg(test)]
            Self::ControlledFixture => true,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Reuse {
    Executed,
    Cached,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Success {
    schema: String,
    authority: String,
    inputs: String,
    outputs: String,
    completed: bool,
}

/// Keep the lease through the final atomic publication, including error paths.
struct Lease(File);

impl Lease {
    fn acquire(dir: &Path) -> Result<Self, String> {
        fs::create_dir_all(dir).map_err(|e| e.to_string())?;
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(dir.join("lock"))
            .map_err(|e| e.to_string())?;
        file.try_lock().map_err(|e| format!("native repository check is already owned: {e}"))?;
        Ok(Self(file))
    }
}

impl Drop for Lease {
    fn drop(&mut self) {
        let _ = self.0.unlock();
    }
}

/// Run one transaction with an explicit reuse policy. Record-only always executes.
/// Clear the old success BEFORE running anything, so a crash cannot resurrect it.
pub(crate) fn run<'a>(
    policy: ReusePolicy,
    dir: &Path,
    outputs: impl Into<OutputNamespace<'a>>,
    snapshot: impl Fn() -> Result<InputSnapshot, String>,
    action: impl FnOnce() -> Result<(), String>,
) -> Result<Reuse, String> {
    run_with_authority(policy, dir, outputs, snapshot, action, AUTHORITY)
}

/// Trust: WP execution is a distinct statement, never a compiler/UI receipt.
pub(crate) fn run_wp<'a>(
    dir: &Path,
    outputs: OutputNamespace<'a>,
    snapshot: impl Fn() -> Result<InputSnapshot, String>,
    action: impl FnOnce() -> Result<(), String>,
) -> Result<Reuse, String> {
    run_with_authority(
        ReusePolicy::RecordOnly,
        dir,
        outputs,
        snapshot,
        action,
        "completed unverified WP workspace release build and library/binary unit tests; no proof claim",
    )
}

fn run_with_authority<'a>(
    policy: ReusePolicy,
    dir: &Path,
    outputs: impl Into<OutputNamespace<'a>>,
    snapshot: impl Fn() -> Result<InputSnapshot, String>,
    action: impl FnOnce() -> Result<(), String>,
    authority: &str,
) -> Result<Reuse, String> {
    let _lease = Lease::acquire(dir)?;
    let outputs = outputs.into();
    let record = dir.join("success.json");
    let before = snapshot()?;
    let previous = policy
        .permits_reuse()
        .then(|| {
            fs::metadata(&record)
                .ok()
                .filter(|metadata| metadata.len() <= 16 * 1024)
                .and_then(|_| fs::read(&record).ok())
                .and_then(|bytes| serde_json::from_slice::<Success>(&bytes).ok())
        })
        .flatten();
    if let Some(previous) = previous {
        if previous.schema == SCHEMA
            && previous.authority == authority
            && previous.completed
            && previous.inputs == before.digest
        {
            if let Ok(observed) = outputs.observe(&before, dir) {
                if observed.digest().ok().as_ref() == Some(&previous.outputs) {
                    if snapshot()? != before {
                        return Err(
                            "inputs moved while validating a cached native repository check".into(),
                        );
                    }
                    if observed.digest()? != previous.outputs {
                        return Err(
                            "outputs moved while validating a cached native repository check"
                                .into(),
                        );
                    }
                    return Ok(Reuse::Cached);
                }
            }
        }
    }
    remove_success(&record)?;
    action()?;
    let observed = outputs.observe(&before, dir)?;
    let output_digest = observed.digest()?;
    if snapshot()? != before {
        return Err("inputs moved during the native repository check; no success was saved".into());
    }
    if observed.digest()? != output_digest {
        return Err(
            "outputs moved while finalizing native repository execution; no success was saved"
                .into(),
        );
    }
    let success = Success {
        schema: SCHEMA.into(),
        authority: authority.into(),
        inputs: before.digest.clone(),
        outputs: output_digest,
        completed: true,
    };
    let mut temporary = tempfile::NamedTempFile::new_in(dir).map_err(|e| e.to_string())?;
    serde_json::to_writer(&mut temporary, &success).map_err(|e| e.to_string())?;
    temporary.write_all(b"\n").map_err(|e| e.to_string())?;
    temporary.as_file().sync_all().map_err(|e| e.to_string())?;
    temporary.persist(&record).map_err(|e| e.to_string())?;
    if let Err(error) = observed.check_namespace() {
        remove_success(&record)?;
        return Err(error);
    }
    #[cfg(unix)]
    File::open(dir).and_then(|file| file.sync_all()).map_err(|e| e.to_string())?;
    Ok(Reuse::Executed)
}

fn remove_success(path: &Path) -> Result<(), String> {
    match fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(e.to_string()),
    }
}

/// Length-prefix every component, so distinct input sequences never alias.
pub(crate) fn add(hash: &mut Sha256, bytes: impl AsRef<[u8]>) {
    let bytes = bytes.as_ref();
    hash.update((bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}

pub(crate) fn finish(hash: Sha256) -> String {
    hex_encode(hash.finalize())
}

pub(crate) fn bytes_digest(bytes: &[u8]) -> String {
    hex_encode(Sha256::digest(bytes))
}

/// Authenticate the bytes through one descriptor and its exact pathname.
pub(crate) fn file_digest(path: &Path) -> Result<String, String> {
    file_digest_with_hooks(path, || {}, || {})
        .map_err(|error| format!("{}: {error}", path.display()))
}

fn file_digest_with_hooks(
    path: &Path,
    after_stat: impl FnOnce(),
    after_read: impl FnOnce(),
) -> Result<String, String> {
    let before = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() {
        return Err(format!("expected an exact regular input file: {}", path.display()));
    }
    after_stat();
    // Trust: a replaced leaf must not follow a symlink or block on a FIFO
    // before the opened-file identity check. std already uses close-on-exec.
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let mut file = options.open(path).map_err(|e| e.to_string())?;
    let opened = file.metadata().map_err(|e| e.to_string())?;
    if !opened.is_file() {
        return Err(format!("opened input is not a regular file: {}", path.display()));
    }
    if !same_snapshot(&before, &opened) {
        return Err(format!("{} was replaced before it was opened", path.display()));
    }
    let mut hash = Sha256::new();
    let mut total = 0_u64;
    let mut buffer = [0_u8; 65536];
    loop {
        let count = file.read(&mut buffer).map_err(|e| e.to_string())?;
        if count == 0 {
            break;
        }
        total = total.checked_add(count as u64).ok_or("input length overflow")?;
        if total > before.len() {
            return Err(format!("{} grew while it was read", path.display()));
        }
        hash.update(&buffer[..count]);
    }
    after_read();
    let opened_after = file.metadata().map_err(|e| e.to_string())?;
    let after = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if total != before.len()
        || !same_snapshot(&before, &opened_after)
        || !same_snapshot(&before, &after)
    {
        return Err(format!("{} moved while it was read", path.display()));
    }
    Ok(hex_encode(hash.finalize()))
}

pub(crate) fn same_snapshot(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        left.dev() == right.dev()
            && left.ino() == right.ino()
            && left.mode() == right.mode()
            && left.len() == right.len()
            && left.mtime() == right.mtime()
            && left.mtime_nsec() == right.mtime_nsec()
            && left.ctime() == right.ctime()
            && left.ctime_nsec() == right.ctime_nsec()
    }
    #[cfg(not(unix))]
    {
        left.file_type() == right.file_type()
            && left.len() == right.len()
            && left.permissions() == right.permissions()
            && left.modified().ok() == right.modified().ok()
            && left.created().ok() == right.created().ok()
    }
}

/// Content, permissions, directory entries and symlink targets all matter. Follow
/// output/dependency links, with a canonical visited set to terminate cycles.
pub(crate) fn tree_digest(root: &Path) -> Result<String, String> {
    let mut hash = Sha256::new();
    hash_path(&mut hash, root, &mut BTreeSet::new(), TreeInputs::Required)?;
    Ok(finish(hash))
}

/// Observe package bytes only after proving that every followed namespace is
/// disjoint from the dedicated output. Content failures disable reuse; failures
/// to inspect the namespace refuse mutation rather than becoming a cache miss.
pub(crate) fn own_cmake_source_digest(
    root: &Path,
    output: &Path,
) -> Result<Option<String>, String> {
    own_cmake_source_digest_with_hook(root, output, || {})
}

fn own_cmake_source_digest_with_hook(
    root: &Path,
    output: &Path,
    after_walk: impl FnOnce(),
) -> Result<Option<String>, String> {
    refuse_in_this_checkout_under_test(root, "hashes CMake sources");
    let source_before = fs::metadata(root).map_err(|e| e.to_string())?;
    if !source_before.is_dir() {
        return Err("CMake source root is not a directory".into());
    }
    let (existing, tail) = existing_output_prefix(output)?;
    let output_before = fs::metadata(&existing).map_err(|e| e.to_string())?;
    let output_route = namespace_route_links([existing.as_path()], 1024)?;
    let source_route = namespace_route_links([root], 1024)?;
    let canonical_prefix = fs::canonicalize(&existing).map_err(|e| e.to_string())?;
    let destination = canonical_prefix.join(&tail);
    let walk = OwnSourceWalk { output: destination, unknown: std::cell::Cell::new(false) };
    let mut hash = Sha256::new();
    hash_path(&mut hash, root, &mut BTreeSet::new(), TreeInputs::OwnSource(&walk))?;
    after_walk();
    if !same_snapshot(&source_before, &fs::metadata(root).map_err(|e| e.to_string())?)
        || !same_snapshot(&output_before, &fs::metadata(&existing).map_err(|e| e.to_string())?)
    {
        return Err("CMake source/output directory moved during observation".into());
    }
    for link in output_route.iter().chain(&source_route) {
        if !same_snapshot(
            &link.metadata,
            &fs::symlink_metadata(&link.path).map_err(|e| e.to_string())?,
        ) || fs::read_link(&link.path).map_err(|e| e.to_string())? != link.target
        {
            return Err("CMake source/output namespace route moved during observation".into());
        }
    }
    let (after, after_tail) = existing_output_prefix(output)?;
    if after != existing
        || after_tail != tail
        || fs::canonicalize(&after).map_err(|e| e.to_string())? != canonical_prefix
    {
        return Err("CMake output namespace moved during source observation".into());
    }
    Ok((!walk.unknown.get()).then(|| finish(hash)))
}

/// Resolve an input/output namespace through its existing ancestor without guessing
/// unresolved parent components. Missing selected inputs still protect their namespace.
pub(crate) fn selected_input_namespace(path: &Path) -> Result<PathBuf, String> {
    if !path.is_absolute()
        || path.components().any(|part| matches!(part, std::path::Component::ParentDir))
    {
        return Err("selected input must be absolute without parent components".into());
    }
    let mut prefix = path.components().collect::<PathBuf>();
    let mut tail = PathBuf::new();
    loop {
        match fs::symlink_metadata(&prefix) {
            Ok(_) => {
                return fs::canonicalize(&prefix)
                    .map(|base| base.join(tail))
                    .map_err(|error| error.to_string());
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                let name =
                    prefix.file_name().ok_or("selected input has no existing ancestor")?.to_owned();
                tail = PathBuf::from(name).join(tail);
                prefix.pop();
            }
            Err(error) => return Err(error.to_string()),
        }
    }
}

// Unlike directory-only installation routes, selected inputs may be files.
// Retain every final-file alias and the directory aliases in each target route.
fn cleanup_route_links(path: &Path) -> Result<Vec<NamespaceRouteLink>, String> {
    if fs::metadata(path).map_err(|error| error.to_string())?.is_dir() {
        return namespace_route_links([path], 1024);
    }
    let mut links = Vec::new();
    let mut leaf = path.to_owned();
    let mut visited = BTreeSet::new();
    loop {
        if !visited.insert(leaf.clone()) || visited.len() > 1024 {
            return Err("selected input alias route exceeds its observation bound".into());
        }
        let parent = leaf.parent().ok_or("selected input has no parent")?;
        links.extend(namespace_route_links([parent], 1024)?);
        if links.len() > 1024 {
            return Err("selected input alias route exceeds its observation bound".into());
        }
        let metadata = fs::symlink_metadata(&leaf).map_err(|error| error.to_string())?;
        if !metadata.file_type().is_symlink() {
            return Ok(links);
        }
        let target = fs::read_link(&leaf).map_err(|error| error.to_string())?;
        let destination = if target.is_absolute() { target.clone() } else { parent.join(&target) };
        links.push(NamespaceRouteLink { path: leaf, metadata, target });
        leaf = destination;
    }
}

struct CleanupPath {
    requested: PathBuf,
    existing: PathBuf,
    metadata: fs::Metadata,
    resolved: PathBuf,
    links: Vec<NamespaceRouteLink>,
}
impl CleanupPath {
    fn observe(path: &Path) -> Result<Self, String> {
        let resolved = selected_input_namespace(path)?;
        let mut existing = path.components().collect::<PathBuf>();
        loop {
            match fs::symlink_metadata(&existing) {
                Ok(metadata) => {
                    let links = cleanup_route_links(&existing)?;
                    return Ok(Self {
                        requested: path.to_owned(),
                        existing,
                        metadata,
                        resolved,
                        links,
                    });
                }
                Err(error) if error.kind() == io::ErrorKind::NotFound => {
                    if !existing.pop() {
                        return Err("selected input has no existing ancestor".into());
                    }
                }
                Err(error) => return Err(error.to_string()),
            }
        }
    }
    fn recheck(&self) -> Result<(), String> {
        if selected_input_namespace(&self.requested)? != self.resolved
            || !same_snapshot(
                &self.metadata,
                &fs::symlink_metadata(&self.existing).map_err(|e| e.to_string())?,
            )
        {
            return Err("selected cleanup namespace moved".into());
        }
        for link in &self.links {
            if !same_snapshot(
                &link.metadata,
                &fs::symlink_metadata(&link.path).map_err(|e| e.to_string())?,
            ) || fs::read_link(&link.path).map_err(|e| e.to_string())? != link.target
            {
                return Err("selected cleanup namespace alias moved".into());
            }
        }
        Ok(())
    }
}

/// The anchor is caller-declared ownership, not evidence inferred from resolving a path.
/// Aliases above it are supported routes; aliases below it forbid replacement.
pub(crate) struct CleanupNamespaces {
    paths: Vec<CleanupPath>,
    pub(crate) linked: bool,
}
impl CleanupNamespaces {
    pub(crate) fn recheck(&self) -> Result<(), String> {
        for path in &self.paths {
            path.recheck()?;
        }
        Ok(())
    }
}
pub(crate) fn cleanup_input_namespaces(
    anchor: &Path,
    output: &Path,
    inputs: &[PathBuf],
) -> Result<CleanupNamespaces, String> {
    let anchor_path = CleanupPath::observe(anchor)?;
    let output_path = CleanupPath::observe(output)?;
    if !output_path.resolved.starts_with(&anchor_path.resolved)
        || output_path.resolved == anchor_path.resolved
    {
        return Err("dedicated output is outside its declared ownership anchor".into());
    }
    let linked = output_path.links.iter().any(|link| {
        (link.path.starts_with(anchor) && link.path != anchor)
            || (link.path.starts_with(&anchor_path.resolved) && link.path != anchor_path.resolved)
    });
    let destination = output_path.resolved.clone();
    let mut paths = vec![anchor_path, output_path];
    for input in inputs {
        let selected = CleanupPath::observe(input)?;
        if selected.resolved.starts_with(&destination)
            || destination.starts_with(&selected.resolved)
        {
            return Err(format!(
                "selected input/output namespace overlap: {} / {}",
                input.display(),
                output.display()
            ));
        }
        paths.push(selected);
    }
    let observed = CleanupNamespaces { paths, linked };
    observed.recheck()?;
    Ok(observed)
}

struct OwnSourceWalk {
    output: PathBuf,
    unknown: std::cell::Cell<bool>,
}

impl OwnSourceWalk {
    fn check(&self, path: &Path) -> Result<(), String> {
        let resolved = fs::canonicalize(path).map_err(|e| e.to_string())?;
        // Trust: every entry the walk visits, a followed link's target included.
        refuse_in_this_checkout_under_test(&resolved, "hashes CMake sources");
        if resolved.starts_with(&self.output) || self.output.starts_with(&resolved) {
            return Err(format!(
                "CMake source and output overlap: {} / {}",
                resolved.display(),
                self.output.display()
            ));
        }
        Ok(())
    }
}

// Reject unresolved parent components instead of guessing how they cross a
// missing directory or alias. Existing ancestor aliases retain their real route.
fn existing_output_prefix(output: &Path) -> Result<(PathBuf, PathBuf), String> {
    if !output.is_absolute()
        || output.components().any(|p| matches!(p, std::path::Component::ParentDir))
    {
        return Err("CMake output must be absolute without unresolved parent components".into());
    }
    // A trailing '/.' makes lstat follow an alias. ParentDir was rejected
    // above; removing only redundant components preserves the actual route.
    let output = output.components().collect::<PathBuf>();
    let mut prefix = output.clone();
    let mut tail = PathBuf::new();
    loop {
        match fs::symlink_metadata(&prefix) {
            Ok(metadata) => {
                if prefix == output && metadata.file_type().is_symlink() {
                    return Err("CMake output root must not be a symlink".into());
                }
                if !fs::metadata(&prefix).map_err(|e| e.to_string())?.is_dir() {
                    return Err("CMake output ancestor is not a directory".into());
                }
                return Ok((prefix, tail));
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                let name =
                    prefix.file_name().ok_or("CMake output has no existing ancestor")?.to_owned();
                tail = PathBuf::from(name).join(tail);
                prefix = prefix.parent().ok_or("CMake output has no parent")?.to_owned();
            }
            Err(error) => return Err(error.to_string()),
        }
    }
}

/// Installed namespaces can contain unused dangling links. Bind those entries
/// and their observed absence without treating them as an available tool or
/// artifact. Required tools/loaders, source trees and outputs use `tree_digest`.
pub(crate) fn installation_tree_digest(root: &Path) -> Result<String, String> {
    let mut hash = Sha256::new();
    add(&mut hash, b"trust.installation-input-tree/v1");
    hash_path(&mut hash, root, &mut BTreeSet::new(), TreeInputs::Installation)?;
    Ok(finish(hash))
}

#[derive(Clone, Copy)]
enum TreeInputs<'a> {
    Required,
    OwnSource(&'a OwnSourceWalk),
    Installation,
    Generated(&'a outputs::GeneratedContext<'a>),
}

fn hash_path(
    hash: &mut Sha256,
    path: &Path,
    seen: &mut BTreeSet<PathBuf>,
    inputs: TreeInputs<'_>,
) -> Result<(), String> {
    hash_path_inner(hash, path, seen, inputs)
        .map_err(|error| format!("{}: {error}", path.display()))
}

fn hash_path_inner(
    hash: &mut Sha256,
    path: &Path,
    seen: &mut BTreeSet<PathBuf>,
    inputs: TreeInputs<'_>,
) -> Result<(), String> {
    if let TreeInputs::Generated(context) = inputs {
        if let Some(digest) = context.leaf(path)? {
            add(hash, digest);
            return Ok(());
        }
    }
    let before = fs::symlink_metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if let TreeInputs::OwnSource(walk) = inputs {
        walk.check(path)?;
    }
    add(hash, path.as_os_str().as_encoded_bytes());
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        add(hash, before.permissions().mode().to_le_bytes());
    }
    #[cfg(not(unix))]
    add(hash, [u8::from(before.permissions().readonly())]);
    if before.file_type().is_symlink() {
        add(hash, b"link");
        let target = fs::read_link(path).map_err(|e| e.to_string())?;
        add(hash, target.as_os_str().as_encoded_bytes());
        let sealed_system_link = cfg!(target_os = "macos")
            && target.is_absolute()
            && !target.components().any(|part| matches!(part, std::path::Component::ParentDir))
            && (target.starts_with("/usr/lib") || target.starts_with("/System/Library"))
            && !path.exists();
        if sealed_system_link && matches!(inputs, TreeInputs::Required | TreeInputs::Generated(_)) {
            // The native key separately binds sw_vers's sealed OS build.
            add(hash, b"sealed-system-shared-cache-link");
        } else {
            match fs::canonicalize(path) {
                Ok(canonical) => {
                    if !seen.contains(&canonical) {
                        hash_path(hash, &canonical, seen, inputs)?;
                    }
                }
                Err(error)
                    if matches!(inputs, TreeInputs::Installation)
                        && error.kind() == io::ErrorKind::NotFound =>
                {
                    add(hash, missing_installation_link_digest_with_hook(path, || {})?);
                }
                Err(error) => return Err(error.to_string()),
            }
        }
    } else if before.is_dir() {
        add(hash, b"directory");
        if !seen.insert(fs::canonicalize(path).map_err(|e| e.to_string())?) {
            return Ok(());
        }
        let mut entries = fs::read_dir(path)
            .map_err(|e| e.to_string())?
            .map(|entry| entry.map(|e| e.path()))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| e.to_string())?;
        entries.sort();
        for entry in entries {
            // Git metadata is not package source; repository HEADs are bound below.
            if !matches!(inputs, TreeInputs::Generated(_))
                && entry.file_name().is_some_and(|name| name == ".git")
            {
                continue;
            }
            hash_path(hash, &entry, seen, inputs)?;
        }
    } else if before.is_file() {
        add(hash, b"file");
        match file_digest(path) {
            Ok(digest) => add(hash, digest),
            Err(_) if matches!(inputs, TreeInputs::OwnSource(_)) => {
                if let TreeInputs::OwnSource(walk) = inputs {
                    walk.unknown.set(true);
                }
            }
            Err(error) => return Err(error),
        }
    } else if let TreeInputs::OwnSource(walk) = inputs {
        walk.unknown.set(true);
    } else {
        return Err(format!("unsupported native repository input: {}", path.display()));
    }
    let after = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !same_snapshot(&before, &after) {
        return Err(format!("{} moved while it was hashed", path.display()));
    }
    Ok(())
}

/// Anchor the nearest existing destination directory, including when the raw
/// destination crosses parent components or another symlink. Retain its FD and
/// re-resolve that namespace after observation: missing parents appearing or
/// being replaced must not silently preserve an earlier absence observation.
fn missing_installation_link_digest_with_hook(
    path: &Path,
    after_open: impl FnOnce(),
) -> Result<String, String> {
    let at_path = |error: io::Error| format!("{}: {error}", path.display());
    let before = fs::symlink_metadata(path).map_err(at_path)?;
    if !before.file_type().is_symlink() {
        return Err(format!("expected an unresolved installation link: {}", path.display()));
    }
    let link = fs::read_link(path).map_err(at_path)?;
    require_missing_resolution(path)?;
    let destination = if link.is_absolute() {
        link.clone()
    } else {
        path.parent().ok_or("installation link has no parent")?.join(&link)
    };
    let mut prefix = destination.as_path();
    let canonical_parent = loop {
        match fs::canonicalize(prefix) {
            Ok(parent) => break parent,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                // A second dangling link can hide a different missing parent
                // behind this lexical prefix. Refuse that unresolved route;
                // this bounded slice records only a directly missing suffix.
                // lstat of "alias/" follows the trailing separator. Probe the
                // same components without redundant separators/dots so that a
                // dangling alias cannot disappear when the lexical parent pops.
                let probe = prefix.components().collect::<PathBuf>();
                match fs::symlink_metadata(&probe) {
                    Ok(metadata) if metadata.file_type().is_symlink() => {
                        return Err(format!(
                            "unsupported secondary unresolved installation link: {}",
                            prefix.display()
                        ));
                    }
                    Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                    Err(error) => return Err(format!("{}: {error}", prefix.display())),
                    Ok(_) => {
                        return Err(format!(
                            "installation namespace moved while resolving {}",
                            prefix.display()
                        ));
                    }
                }
                prefix = prefix.parent().ok_or_else(|| {
                    format!(
                        "unresolved installation link has no existing namespace: {}",
                        path.display()
                    )
                })?;
            }
            Err(error) => return Err(at_path(error)),
        }
    };
    let parent_before = fs::symlink_metadata(&canonical_parent).map_err(at_path)?;
    if !parent_before.is_dir() || parent_before.file_type().is_symlink() {
        return Err(format!(
            "installation link namespace is not an exact directory: {}",
            path.display()
        ));
    }
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let parent = options.open(&canonical_parent).map_err(at_path)?;
    let opened = parent.metadata().map_err(at_path)?;
    if !opened.is_dir() || !same_snapshot(&parent_before, &opened) {
        return Err(format!(
            "installation link namespace moved before opening: {}",
            path.display()
        ));
    }
    let route = namespace_route_links(
        [prefix, path.parent().ok_or("installation link has no parent")?],
        4096,
    )?;
    after_open();
    require_missing_resolution(path)?;
    if !same_snapshot(&before, &fs::symlink_metadata(path).map_err(at_path)?)
        || fs::read_link(path).map_err(at_path)? != link
        || fs::canonicalize(prefix).map_err(at_path)? != canonical_parent
        || !same_snapshot(&opened, &parent.metadata().map_err(at_path)?)
        || !same_snapshot(&opened, &fs::symlink_metadata(&canonical_parent).map_err(at_path)?)
        || !same_snapshot(&before, &fs::symlink_metadata(path).map_err(at_path)?)
    {
        return Err(format!("installation link or missing namespace moved: {}", path.display()));
    }
    for link in &route {
        if !same_snapshot(
            &link.metadata,
            &fs::symlink_metadata(&link.path)
                .map_err(|error| format!("{}: {error}", link.path.display()))?,
        ) || fs::read_link(&link.path)
            .map_err(|error| format!("{}: {error}", link.path.display()))?
            != link.target
            || !same_snapshot(
                &link.metadata,
                &fs::symlink_metadata(&link.path)
                    .map_err(|error| format!("{}: {error}", link.path.display()))?,
            )
        {
            return Err(format!("installation namespace route moved: {}", link.path.display()));
        }
    }
    let mut hash = Sha256::new();
    add(&mut hash, b"trust.installation-missing-link/v1");
    add(&mut hash, path.as_os_str().as_encoded_bytes());
    add(&mut hash, link.as_os_str().as_encoded_bytes());
    add(&mut hash, prefix.as_os_str().as_encoded_bytes());
    add(&mut hash, canonical_parent.as_os_str().as_encoded_bytes());
    add(
        &mut hash,
        destination.strip_prefix(prefix).map_err(|e| e.to_string())?.as_os_str().as_encoded_bytes(),
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        add(&mut hash, before.permissions().mode().to_le_bytes());
        add(&mut hash, opened.permissions().mode().to_le_bytes());
    }
    #[cfg(not(unix))]
    {
        add(&mut hash, [u8::from(before.permissions().readonly())]);
        add(&mut hash, [u8::from(opened.permissions().readonly())]);
    }
    for link in route {
        add(&mut hash, link.path.as_os_str().as_encoded_bytes());
        add(&mut hash, link.target.as_os_str().as_encoded_bytes());
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            add(&mut hash, link.metadata.permissions().mode().to_le_bytes());
        }
        #[cfg(not(unix))]
        add(&mut hash, [u8::from(link.metadata.permissions().readonly())]);
    }
    Ok(finish(hash))
}

#[derive(Debug)]
struct NamespaceRouteLink {
    path: PathBuf,
    metadata: fs::Metadata,
    target: PathBuf,
}

/// Observe resolved ancestor aliases, including aliases in their own targets.
/// Canonical-parent equality alone misses an alias replaced with another link
/// to that very same directory. Every visited prefix must still resolve.
fn namespace_route_links<'a>(
    paths: impl IntoIterator<Item = &'a Path>,
    limit: usize,
) -> Result<Vec<NamespaceRouteLink>, String> {
    let mut pending = paths.into_iter().map(Path::to_owned).collect::<Vec<_>>();
    let mut visited = BTreeSet::new();
    let mut links = Vec::new();
    while let Some(path) = pending.pop() {
        for prefix in path.ancestors() {
            // Trailing '/' or '/.' otherwise makes lstat follow this alias.
            // Keep ParentDir components and raw target bytes, but inspect and
            // retain the actual symlink node at every collected prefix.
            let prefix = prefix.components().collect::<PathBuf>();
            if !visited.insert(prefix.to_owned()) {
                continue;
            }
            if visited.len() > limit {
                return Err("installation namespace route exceeds its observation bound".into());
            }
            let metadata = fs::symlink_metadata(&prefix)
                .map_err(|error| format!("{}: {error}", prefix.display()))?;
            if metadata.file_type().is_symlink() {
                let target = fs::read_link(&prefix)
                    .map_err(|error| format!("{}: {error}", prefix.display()))?;
                let destination = if target.is_absolute() {
                    target.clone()
                } else {
                    prefix.parent().ok_or("namespace alias has no parent")?.join(&target)
                };
                pending.push(destination);
                links.push(NamespaceRouteLink { path: prefix.to_owned(), metadata, target });
            } else if !metadata.is_dir() {
                return Err(format!(
                    "installation namespace route is not a directory: {}",
                    prefix.display()
                ));
            }
        }
    }
    links.sort_by(|left, right| left.path.cmp(&right.path));
    Ok(links)
}

fn require_missing_resolution(path: &Path) -> Result<(), String> {
    match fs::canonicalize(path) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!("{}: {error}", path.display())),
        Ok(_) => {
            Err(format!("installation link no longer has a missing resolution: {}", path.display()))
        }
    }
}

/// Conservative source closure: every tracked path and every non-ignored new
/// path, recursively through exact gitlinks. No extension/path selector can hide
/// a runtime fixture read. Ignored configuration/seed/dependency inputs are added
/// explicitly by the caller; this is not a claim of hermetic execution.
pub(crate) fn repository_digest(root: &Path, jobs: usize) -> Result<String, String> {
    let mut hash = Sha256::new();
    repository(&mut hash, root, jobs, &repository_leaf)?;
    Ok(finish(hash))
}

#[derive(Debug)]
enum RepositoryLeaf {
    Digest(String),
    Gitlink,
}

/// Hash leaves with at most the caller's parsed jobs budget, including this thread.
/// Keep only per-leaf results, never file contents, and restore inventory order before
/// examining errors or folding digests. Scoped workers always finish before return.
pub(crate) fn hash_leaves<T: Send>(
    paths: &[PathBuf],
    jobs: usize,
    leaf: impl Fn(&Path) -> Result<T, String> + Sync,
) -> Result<Vec<T>, String> {
    if jobs == 0 {
        return Err("native repository hashing requires a positive parsed jobs budget".into());
    }
    let jobs = jobs.min(paths.len());
    if jobs <= 1 {
        return paths.iter().map(|path| leaf(path)).collect();
    }
    let next = AtomicUsize::new(0);
    let work = || {
        let mut results = Vec::new();
        loop {
            let index = next.fetch_add(1, Ordering::Relaxed);
            let Some(path) = paths.get(index) else { break };
            results.push((index, leaf(path)));
        }
        results
    };
    let mut results = std::thread::scope(|scope| {
        let mut workers = Vec::new();
        let mut failure = None;
        for _ in 1..jobs {
            match std::thread::Builder::new().name("repo-hash".into()).spawn_scoped(scope, &work) {
                Ok(worker) => workers.push(worker),
                Err(error) => {
                    failure = Some(format!("cannot start native repository hash worker: {error}"));
                    break;
                }
            }
        }
        let mut results = work();
        for worker in workers {
            match worker.join() {
                Ok(mut leaves) => results.append(&mut leaves),
                Err(_) => failure = Some("native repository hash worker panicked".into()),
            }
        }
        failure.map_or(Ok(results), Err)
    })?;
    results.sort_unstable_by_key(|(index, _)| *index);
    results.into_iter().map(|(_, result)| result).collect()
}

fn repository(
    hash: &mut Sha256,
    root: &Path,
    jobs: usize,
    leaf: &(impl Fn(&Path, &Path, &BTreeSet<PathBuf>) -> Result<RepositoryLeaf, String> + Sync),
) -> Result<(), String> {
    let head = git(root, &["rev-parse", "--verify", "HEAD^{commit}"])?;
    add(hash, &head);
    let entries = git(root, &["ls-files", "--stage", "-z"])?;
    let mut paths = BTreeSet::new();
    let mut gitlinks = BTreeSet::new();
    for entry in entries.split(|&byte| byte == 0).filter(|entry| !entry.is_empty()) {
        let text = std::str::from_utf8(entry).map_err(|e| e.to_string())?;
        let (metadata, path) = text.split_once('\t').ok_or("invalid Git input inventory")?;
        let fields = metadata.split_whitespace().collect::<Vec<_>>();
        if fields.len() != 3 || fields[2] != "0" {
            return Err("unmerged Git input cannot name a native repository check".into());
        }
        add(hash, entry);
        let path = root.join(path);
        paths.insert(path.clone());
        if fields[0] == "160000" {
            gitlinks.insert(path.clone());
            let actual = git(&path, &["rev-parse", "--verify", "HEAD^{commit}"])?;
            if std::str::from_utf8(&actual).map_err(|e| e.to_string())?.trim() != fields[1] {
                return Err(format!("submodule {} does not match its pin", path.display()));
            }
            // Finish the child's entire batch before starting this repository's
            // workers: nested repositories never multiply the jobs budget.
            repository(hash, &path, jobs, leaf)?;
        }
    }
    let untracked = git(root, &["ls-files", "--others", "--exclude-standard", "-z"])?;
    for path in untracked.split(|&byte| byte == 0).filter(|path| !path.is_empty()) {
        let path = std::str::from_utf8(path).map_err(|e| e.to_string())?;
        paths.insert(root.join(path));
    }
    let paths = paths.into_iter().collect::<Vec<_>>();
    let leaves = hash_leaves(&paths, jobs, |path| leaf(root, path, &gitlinks))?;
    for leaf in leaves {
        match leaf {
            RepositoryLeaf::Digest(digest) => add(hash, digest),
            RepositoryLeaf::Gitlink => {}
        }
    }
    if git(root, &["rev-parse", "--verify", "HEAD^{commit}"])? != head {
        return Err("HEAD moved while naming native repository inputs".into());
    }
    Ok(())
}

fn repository_leaf(
    root: &Path,
    path: &Path,
    gitlinks: &BTreeSet<PathBuf>,
) -> Result<RepositoryLeaf, String> {
    if path.is_dir() && !path.is_symlink() {
        if gitlinks.contains(path) {
            return Ok(RepositoryLeaf::Gitlink);
        }
        return Err(format!("unexpected directory in the Git leaf inventory: {}", path.display()));
    }
    if path.is_symlink() && path.is_dir() {
        return source_directory_link_digest_with_hook(root, path, || {})
            .map(RepositoryLeaf::Digest);
    }
    tree_digest(path).map(RepositoryLeaf::Digest)
}

/// Bind an alias into this repository's already inventoried source namespace.
/// Its tracked/non-ignored leaves are hashed by `repository`, not by following
/// the alias into ignored build trees, Git metadata or ancestor cycles. This
/// remains an observed Git inventory, never a complete arbitrary read closure.
fn source_directory_link_digest_with_hook(
    root: &Path,
    path: &Path,
    after_open: impl FnOnce(),
) -> Result<String, String> {
    let root = fs::canonicalize(root).map_err(|e| e.to_string())?;
    let before = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !before.file_type().is_symlink() {
        return Err(format!("expected a source directory alias: {}", path.display()));
    }
    let link = fs::read_link(path).map_err(|e| e.to_string())?;
    let target = fs::canonicalize(path).map_err(|e| e.to_string())?;
    if !target.starts_with(&root) {
        return Err(format!("source directory alias escapes its repository: {}", path.display()));
    }
    let target_before = fs::symlink_metadata(&target).map_err(|e| e.to_string())?;
    if !target_before.is_dir() || target_before.file_type().is_symlink() {
        return Err(format!("source alias target is not an exact directory: {}", path.display()));
    }
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let directory = options.open(&target).map_err(|e| e.to_string())?;
    let opened = directory.metadata().map_err(|e| e.to_string())?;
    if !opened.is_dir() || !same_snapshot(&target_before, &opened) {
        return Err(format!(
            "source directory alias target moved before opening: {}",
            path.display()
        ));
    }
    after_open();
    if !same_snapshot(&before, &fs::symlink_metadata(path).map_err(|e| e.to_string())?)
        || fs::read_link(path).map_err(|e| e.to_string())? != link
        || fs::canonicalize(path).map_err(|e| e.to_string())? != target
        || !same_snapshot(&opened, &directory.metadata().map_err(|e| e.to_string())?)
        || !same_snapshot(&opened, &fs::symlink_metadata(&target).map_err(|e| e.to_string())?)
    {
        return Err(format!("source directory alias moved while naming it: {}", path.display()));
    }
    let mut hash = Sha256::new();
    add(&mut hash, b"source-directory-alias/v1");
    add(&mut hash, path.as_os_str().as_encoded_bytes());
    add(&mut hash, link.as_os_str().as_encoded_bytes());
    add(&mut hash, target.as_os_str().as_encoded_bytes());
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        add(&mut hash, before.permissions().mode().to_le_bytes());
        add(&mut hash, opened.permissions().mode().to_le_bytes());
    }
    #[cfg(not(unix))]
    {
        add(&mut hash, [u8::from(before.permissions().readonly())]);
        add(&mut hash, [u8::from(opened.permissions().readonly())]);
    }
    Ok(finish(hash))
}

// Trust: no unit test runs git in this checkout. The landing gate's audit rows
// of this file and of install/wp/transaction.rs (scripts/gates/land-escape-audits.toml)
// declare that bootstrap's tests read neither its tree nor its history; this holds
// it whoever calls. A root that does not resolve is left to git, which fails on it.
fn refuse_this_checkout_under_test(root: &Path) {
    refuse_in_this_checkout_under_test(root, "runs git");
}

// Trust: under cfg(test) only, panics when `path` resolves inside this checkout,
// naming what the unit test would have done there. Other builds return at once.
fn refuse_in_this_checkout_under_test(path: &Path, what: &str) {
    if !cfg!(test) {
        return;
    }
    let checkout = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    if let (Ok(path), Ok(checkout)) = (path.canonicalize(), checkout.canonicalize()) {
        assert!(
            !path.starts_with(&checkout),
            "a unit test never {what} in this checkout ({})",
            path.display()
        );
    }
}

// Trust: installation's clean/HEAD checks must use the exact same Git authority.
pub(crate) fn git_command(root: &Path) -> Command {
    refuse_this_checkout_under_test(root);
    let mut command = Command::new("git");
    for (key, _) in std::env::vars_os() {
        if key.to_str().is_some_and(|key| key.starts_with("GIT_")) {
            command.env_remove(key);
        }
    }
    command.args(["--literal-pathspecs", "-c", "core.fsmonitor=false", "-C"]).arg(root);
    command
}

pub(crate) fn git(root: &Path, args: &[&str]) -> Result<Vec<u8>, String> {
    crate::utils::exec::require_standalone_process("repository input Git query")
        .map_err(|error| error.to_string())?;
    let output = git_command(root).args(args).output().map_err(|e| e.to_string())?;
    if !output.status.success() {
        return Err(format!("cannot inventory native repository inputs at {}", root.display()));
    }
    Ok(output.stdout)
}

#[cfg(test)]
mod tests;

#[cfg(test)]
// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires: the file sits
// under trust_repo_cache/tests/ so the module keeps its `own_source_tests` path.
#[path = "trust_repo_cache/tests/own_source_tests.rs"]
mod own_source_tests;
