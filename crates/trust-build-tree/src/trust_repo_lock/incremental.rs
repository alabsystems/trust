//! Reclaim only this repository's rebuildable crates/target*/debug/incremental.
//!
//! Original root/profile identities and every Cargo profile lock remain held
//! across the rename. Deletion happens after releasing those locks, so the next
//! build can create a fresh cache. Participating builders must honor Cargo's
//! profile locks; hostile concurrent directory renames are outside this protocol.

use std::collections::HashSet;
use std::fs::{self, File, Metadata, OpenOptions};
use std::io;
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use super::{Root, open_directory, same_inode};

const GIB: u64 = 1024 * 1024 * 1024;
const LOCKS: [&str; 3] = [".cargo-lock", ".cargo-build-lock", ".cargo-artifact-lock"];
const PREFIX: &str = "incremental.reclaim-";
const RECLAIMER_LOCK: &str = ".trust-incremental-reclaim.lock";

#[derive(Clone, Copy, Debug)]
pub struct Thresholds {
    pub max_cache_bytes: u64,
    pub min_free_bytes: u64,
}
impl Default for Thresholds {
    fn default() -> Self {
        Self { max_cache_bytes: 50 * GIB, min_free_bytes: 100 * GIB }
    }
}
impl Thresholds {
    fn selected(self, size: u64, free: u64) -> bool {
        size >= self.max_cache_bytes || (size >= GIB && free < self.min_free_bytes)
    }
}

// Bounds are checked between synchronous filesystem observations; they do not
// promise to interrupt a stalled kernel filesystem operation.
struct WalkBudget {
    remaining: usize,
    max_depth: usize,
    until: Instant,
}
impl WalkBudget {
    fn new() -> Self {
        Self {
            remaining: 1_000_000,
            max_depth: 256,
            until: Instant::now() + Duration::from_secs(30),
        }
    }
    fn visit(&mut self, depth: usize) -> io::Result<()> {
        self.check_time()?;
        if self.remaining == 0 || depth > self.max_depth {
            return Err(invalid("incremental observation exceeded its entry/depth/time budget"));
        }
        self.remaining -= 1;
        Ok(())
    }
    fn check_time(&self) -> io::Result<()> {
        if Instant::now() >= self.until {
            return Err(invalid("incremental observation exceeded its time budget"));
        }
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Kept,
    WouldReclaim,
    Busy,
    Reclaimed,
    Refused(String),
}

#[derive(Debug)]
pub struct Observation {
    pub cache: PathBuf,
    pub allocated_bytes: Option<u64>,
    pub free_bytes: Option<u64>,
    pub interrupted_reclaims: usize,
    pub removed_interrupted_reclaims: usize,
    pub outcome: Outcome,
}

fn invalid(reason: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason.into())
}

/// Inspect or reclaim only the selected repository's crates workspace cache.
/// No process is signalled, no lock is forced, and no sysroot/build tree is a
/// candidate. Unknown sizes, free space or directory identities refuse a row.
pub fn reclaim(root: &Path, thresholds: Thresholds, apply: bool) -> io::Result<Vec<Observation>> {
    reclaim_with_cleanup(root, thresholds, apply, &mut |path| fs::remove_dir_all(path))
}

fn reclaim_with_cleanup(
    root: &Path,
    thresholds: Thresholds,
    apply: bool,
    cleanup: &mut dyn FnMut(&Path) -> io::Result<()>,
) -> io::Result<Vec<Observation>> {
    reclaim_with_budget_and_cleanup(root, thresholds, apply, cleanup, &mut WalkBudget::new())
}

fn reclaim_with_budget_and_cleanup(
    root: &Path,
    thresholds: Thresholds,
    apply: bool,
    cleanup: &mut dyn FnMut(&Path) -> io::Result<()>,
    budget: &mut WalkBudget,
) -> io::Result<Vec<Observation>> {
    budget.check_time()?;
    let root = Root::open(root).map_err(invalid)?;
    root.check_current().map_err(invalid)?;
    let crates = root.physical.join("crates");
    match fs::symlink_metadata(&crates) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(error) => return Err(error),
        Ok(metadata) if !metadata.is_dir() => {
            return Err(invalid("crates must be a real directory"));
        }
        Ok(_) => {}
    }
    let crates_file = open_directory(&crates).map_err(invalid)?;
    let crates_identity = crates_file.metadata()?;
    let mut targets = Vec::new();
    for entry in fs::read_dir(&crates)? {
        budget.visit(0)?;
        let entry = entry?;
        if entry.file_name().as_encoded_bytes().starts_with(b"target") {
            if targets.len() >= 4096 {
                return Err(invalid(
                    "incremental observation exceeded its target-directory budget",
                ));
            }
            targets.push(entry);
        }
    }
    targets.sort_by_key(|entry| entry.file_name());
    let mut seen = HashSet::new();
    let mut result = Vec::new();
    for target in targets {
        let logical = target.path().join("debug");
        let mut row = Observation {
            cache: logical.join("incremental"),
            allocated_bytes: None,
            free_bytes: None,
            interrupted_reclaims: 0,
            removed_interrupted_reclaims: 0,
            outcome: Outcome::Kept,
        };
        if let Err(error) = budget.visit(0) {
            row.outcome = Outcome::Refused(error.to_string());
            result.push(row);
            continue;
        }
        let profile = match fs::canonicalize(&logical) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => {
                row.outcome = Outcome::Refused(error.to_string());
                result.push(row);
                continue;
            }
            Ok(profile) => profile,
        };
        // Only target aliases that resolve to a direct target* child of this
        // pinned crates directory are supported. In particular build/sysroots
        // and external target roots are never traversed or reclaimed.
        let permitted = profile.file_name().is_some_and(|name| name == "debug")
            && profile.parent().and_then(Path::parent) == Some(crates.as_path())
            && profile
                .parent()
                .and_then(Path::file_name)
                .is_some_and(|name| name.as_encoded_bytes().starts_with(b"target"));
        if !permitted {
            row.outcome = Outcome::Refused("target resolves outside crates/target*/debug".into());
            result.push(row);
            continue;
        }
        if !seen.insert(profile.clone()) {
            continue;
        }
        row.cache = profile.join("incremental");
        if let Err(error) = inspect_profile(
            ProfileInputs {
                root: &root,
                crates: &crates,
                crates_identity: &crates_identity,
                crates_file: &crates_file,
                thresholds,
                apply,
            },
            &profile,
            &mut row,
            cleanup,
            budget,
        ) {
            row.outcome = Outcome::Refused(error.to_string());
        }
        result.push(row);
    }
    Ok(result)
}

struct ProfileInputs<'a> {
    root: &'a Root,
    crates: &'a Path,
    crates_identity: &'a Metadata,
    crates_file: &'a File,
    thresholds: Thresholds,
    apply: bool,
}

fn inspect_profile(
    inputs: ProfileInputs<'_>,
    profile: &Path,
    row: &mut Observation,
    cleanup: &mut dyn FnMut(&Path) -> io::Result<()>,
    budget: &mut WalkBudget,
) -> io::Result<()> {
    let ProfileInputs { root, crates, crates_identity, crates_file, thresholds, apply } = inputs;
    let directory = open_directory(profile).map_err(invalid)?;
    let identity = directory.metadata()?;
    let check = || {
        root.check_current().map_err(invalid)?;
        for (path, expected, held) in
            [(crates, crates_identity, crates_file), (profile, &identity, &directory)]
        {
            if !same_inode(expected, Some(&fs::symlink_metadata(path)?))
                || !same_inode(expected, Some(&held.metadata()?))
            {
                return Err(invalid("incremental cache directory mapping changed"));
            }
        }
        Ok(())
    };
    check()?;
    // A busy writer is observed before recursively walking its growing cache.
    // The separate reclaimer guard spans deletion, while Cargo's three locks
    // protect only observation/selection/rename and are released before delete.
    let _reclaimer = if apply {
        let Some(lock) = try_lock_file(&profile.join(RECLAIMER_LOCK))? else {
            row.outcome = Outcome::Busy;
            return Ok(());
        };
        Some(lock)
    } else {
        None
    };
    let locks = if apply {
        let Some(locks) = profile_locks(profile)? else {
            row.outcome = Outcome::Busy;
            return Ok(());
        };
        Some(locks)
    } else {
        None
    };
    check()?;
    let mut stale = Vec::new();
    for entry in fs::read_dir(profile)? {
        budget.visit(0)?;
        let entry = entry?;
        if entry.file_name().as_encoded_bytes().starts_with(PREFIX.as_bytes()) {
            let metadata = fs::symlink_metadata(entry.path())?;
            if !metadata.is_dir() || metadata.uid() != unsafe { libc::geteuid() } {
                return Err(invalid("interrupted reclaim must be an owned real directory"));
            }
            stale.push((entry.path(), metadata));
        }
    }
    row.interrupted_reclaims = stale.len();
    let size = cache_bytes_with_budget(&row.cache, budget)?;
    let free = free_bytes(&directory)?;
    // A final synchronous observation can return after its deadline. Check
    // time without consuming another entry from an otherwise complete census.
    budget.check_time()?;
    row.allocated_bytes = Some(size);
    row.free_bytes = Some(free);
    if !apply {
        if thresholds.selected(size, free) && row.cache.exists() {
            row.outcome = Outcome::WouldReclaim;
        }
        return Ok(());
    }
    if !thresholds.selected(size, free) && stale.is_empty() {
        return Ok(());
    }
    // Validate all detached names while the same original profile is still
    // exclusively admitted. Another native reclaimer cannot claim these names
    // while our separate reclaimer guard is retained.
    for (path, expected) in &stale {
        check()?;
        if !same_inode(expected, Some(&fs::symlink_metadata(path)?)) {
            return Err(invalid("interrupted reclaim directory changed"));
        }
    }
    let retired = if thresholds.selected(size, free) && row.cache.exists() {
        let cache_identity = fs::symlink_metadata(&row.cache)?;
        if !cache_identity.is_dir() || cache_identity.uid() != unsafe { libc::geteuid() } {
            return Err(invalid("incremental must be an owned real directory"));
        }
        let garbage = tempfile::Builder::new().prefix(PREFIX).tempdir_in(profile)?;
        check()?;
        if !same_inode(&cache_identity, Some(&fs::symlink_metadata(&row.cache)?)) {
            return Err(invalid("incremental cache changed before rename"));
        }
        budget.check_time()?;
        fs::rename(&row.cache, garbage.path())?;
        // Preserve the exact orphan after any later validation failure; an
        // automatic TempDir drop must never delete through an uncertain name.
        Some((garbage.keep(), cache_identity))
    } else {
        None
    };
    drop(locks);
    for (path, expected) in &stale {
        check()?;
        if !same_inode(expected, Some(&fs::symlink_metadata(path)?)) {
            return Err(invalid("interrupted reclaim changed before deletion"));
        }
        cleanup(path)?;
        row.removed_interrupted_reclaims += 1;
    }
    if let Some((garbage, expected)) = retired {
        check()?;
        if !same_inode(&expected, Some(&fs::symlink_metadata(&garbage)?)) {
            return Err(invalid("renamed incremental cache changed before deletion"));
        }
        cleanup(&garbage)?;
        row.outcome = Outcome::Reclaimed;
    }
    Ok(())
}

fn profile_locks(profile: &Path) -> io::Result<Option<Vec<File>>> {
    let mut held = Vec::new();
    for name in LOCKS {
        let Some(file) = try_lock_file(&profile.join(name))? else { return Ok(None) };
        held.push(file);
    }
    Ok(Some(held))
}

fn try_lock_file(path: &Path) -> io::Result<Option<File>> {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
        .open(path)?;
    let metadata = file.metadata()?;
    if !metadata.is_file()
        || metadata.nlink() != 1
        || metadata.uid() != unsafe { libc::geteuid() }
        || !same_inode(&metadata, Some(&fs::symlink_metadata(path)?))
    {
        return Err(invalid("Cargo lock is not an owned stable regular file"));
    }
    if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        let error = io::Error::last_os_error();
        if error.kind() == io::ErrorKind::WouldBlock {
            return Ok(None);
        }
        return Err(error);
    }
    Ok(Some(file))
}

fn free_bytes(directory: &File) -> io::Result<u64> {
    let mut stats = std::mem::MaybeUninit::<libc::statvfs>::uninit();
    if unsafe { libc::fstatvfs(directory.as_raw_fd(), stats.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let stats = unsafe { stats.assume_init() };
    checked_free_product(stats.f_bavail, stats.f_frsize)
}

// statvfs integer widths/signedness vary across supported Unix libc ABIs.
// Keep the checked conversion and product in one type-independent operation.
fn checked_free_product<A: TryInto<u64>, B: TryInto<u64>>(blocks: A, size: B) -> io::Result<u64> {
    blocks
        .try_into()
        .ok()
        .and_then(|blocks| size.try_into().ok().and_then(|size| blocks.checked_mul(size)))
        .ok_or_else(|| invalid("filesystem free-space observation overflowed"))
}

#[cfg(test)]
fn cache_bytes(cache: &Path) -> io::Result<u64> {
    cache_bytes_with_budget(cache, &mut WalkBudget::new())
}

fn cache_bytes_with_budget(cache: &Path, budget: &mut WalkBudget) -> io::Result<u64> {
    budget.visit(0)?;
    match fs::symlink_metadata(cache) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(0),
        Err(error) => return Err(error),
        Ok(metadata) if !metadata.is_dir() => {
            return Err(invalid("incremental is not a real directory"));
        }
        Ok(_) => {}
    }
    let mut seen = HashSet::new();
    let mut pending = vec![(cache.to_owned(), 0)];
    let mut bytes = 0u64;
    while let Some((path, depth)) = pending.pop() {
        for entry in fs::read_dir(path)? {
            budget.visit(depth + 1)?;
            let entry = entry?;
            let metadata = fs::symlink_metadata(entry.path())?;
            if !seen.insert((metadata.dev(), metadata.ino())) {
                continue;
            }
            let allocated = metadata
                .blocks()
                .checked_mul(512)
                .ok_or_else(|| invalid("incremental allocation overflowed"))?;
            bytes = bytes
                .checked_add(allocated)
                .ok_or_else(|| invalid("incremental cache size overflowed"))?;
            if metadata.is_dir() {
                if pending.len() >= 4096 {
                    return Err(invalid(
                        "incremental observation exceeded its pending-directory budget",
                    ));
                }
                pending.push((entry.path(), depth + 1));
            }
        }
    }
    Ok(bytes)
}

#[cfg(test)]
mod tests;
