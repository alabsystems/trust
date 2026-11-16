// Copyright 2026 Andrew Yates
// Installed-membership observations, not artifact authentication or admission.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use std::path::{Component, Path, PathBuf};

use super::{BuildStamp, bounded_native_evidence};

const MAX_MANIFEST: u64 = 4 * 1024 * 1024;
const MAX_ENTRIES: usize = 64 * 1024;
const MAX_PATH: usize = 16 * 1024;
const RECORD: &str = ".trust-installed-outputs";

// Resolve only paths already proved lexically inside root. Never stat an
// outside symlink target. Re-observation is a bookend, not hostile-swap safety.
fn member(root: &Path, relative: &Path) -> Option<()> {
    let mut pending: VecDeque<_> =
        relative.components().map(|c| c.as_os_str().to_owned()).collect();
    let mut current = root.to_owned();
    let mut links = 0;
    let mut steps = 0;
    while let Some(part) = pending.pop_front() {
        steps += 1;
        if steps > 4096 {
            return None;
        }
        if part == "." {
            continue;
        }
        if part == ".." {
            if current == root || !current.pop() {
                return None;
            }
            continue;
        }
        current.push(part);
        let meta = fs::symlink_metadata(&current).ok()?;
        if meta.file_type().is_symlink() {
            links += 1;
            if links > 64 {
                return None;
            }
            let target = fs::read_link(&current).ok()?;
            if target.as_os_str().len() > MAX_PATH {
                return None;
            }
            let suffix = if target.is_absolute() {
                current = root.to_owned();
                target.strip_prefix(root).ok()?
            } else {
                current.pop();
                &target
            };
            let mut replacement: VecDeque<_> =
                suffix.components().map(|c| c.as_os_str().to_owned()).collect();
            replacement.append(&mut pending);
            pending = replacement;
        } else if pending.is_empty() {
            if !meta.file_type().is_file() {
                return None;
            }
        } else if !meta.file_type().is_dir() {
            return None;
        }
    }
    // Only after every route is proved inside root, ask the OS about the
    // original spelling too: components() erases terminal directory demands.
    (current != root
        && fs::symlink_metadata(&current).ok()?.file_type().is_file()
        && fs::metadata(root.join(relative)).ok()?.is_file())
    .then_some(())
}

fn paths(
    root: &Path,
    selected: &Path,
    bytes: &[u8],
) -> Option<BTreeMap<PathBuf, BTreeSet<String>>> {
    if bytes.is_empty() || bytes.len() > MAX_MANIFEST as usize {
        return None;
    }
    let text = std::str::from_utf8(bytes).ok()?;
    let mut rows: BTreeMap<PathBuf, BTreeSet<String>> = BTreeMap::new();
    let mut count = 0;
    for line in text.split_terminator('\n') {
        count += 1;
        if count > MAX_ENTRIES || line.is_empty() || line.len() > MAX_PATH || line.contains('\0') {
            return None;
        }
        let path = Path::new(line);
        if !path.is_absolute() || path.components().any(|c| matches!(c, Component::ParentDir)) {
            return None;
        }
        let normalized: PathBuf = path.components().collect();
        let relative =
            normalized.strip_prefix(root).or_else(|_| normalized.strip_prefix(selected)).ok()?;
        if relative.as_os_str().is_empty() {
            return None;
        }
        rows.entry(relative.to_owned()).or_default().insert(line.to_owned());
    }
    (!rows.is_empty()).then_some(rows)
}

/// Snapshot the actual install list and require every selected installed file.
/// Bytes of members are deliberately not hashed or authenticated.
pub(super) fn observe(root: &Path, completion: &str) -> Option<Vec<u8>> {
    use sha2::Digest;

    use crate::utils::trust_repo_cache::{add, finish, same_snapshot};
    let selected = root;
    let root = fs::canonicalize(selected).ok()?;
    if !fs::symlink_metadata(&root).ok()?.file_type().is_dir() {
        return None;
    }
    let manifest = root.join("build/install_manifest.txt");
    // The manifest itself must not route through an outside directory alias.
    member(&root, Path::new("build/install_manifest.txt"))?;
    let (bytes, meta) = bounded_native_evidence(&manifest, MAX_MANIFEST)?;
    let rows = paths(&root, selected, &bytes)?;
    let mut hash = sha2::Sha256::new();
    add(&mut hash, b"trust.local-cmake-installed-outputs/v1");
    add(&mut hash, completion.as_bytes());
    add(&mut hash, &(rows.len() as u64).to_le_bytes());
    for (path, spellings) in &rows {
        member(&root, path)?;
        // Validate every original row, including duplicate normalized members.
        // The preceding route proof makes this an owned namespace observation;
        // this does not defend against hostile concurrent link replacement.
        for spelling in spellings {
            if !fs::metadata(spelling).ok()?.is_file() {
                return None;
            }
        }
        add(&mut hash, path.as_os_str().as_encoded_bytes());
    }
    if !same_snapshot(&meta, &fs::symlink_metadata(&manifest).ok()?)
        || fs::canonicalize(selected).ok()? != root
    {
        return None;
    }
    Some(format!("trust.local-cmake-installed-outputs/v1\n{}\n", finish(hash)).into_bytes())
}

pub(super) fn matches(root: &Path, completion: &str) -> Option<Vec<u8>> {
    let expected = observe(root, completion)?;
    let (stored, _) = bounded_native_evidence(&root.join(RECORD), 256)?;
    (stored == expected).then_some(expected)
}

pub(super) fn publish(stamp: &BuildStamp) -> std::io::Result<bool> {
    use std::io::Write;
    let root = stamp.path().parent().unwrap();
    let Some(bytes) = observe(root, stamp.stamp()) else {
        return Ok(false);
    };
    // Refuse aliases for the record; never interpret a miss as cleanup authority.
    match fs::symlink_metadata(root.join(RECORD)) {
        Ok(meta) if !meta.file_type().is_file() => return Ok(false),
        Err(error) if error.kind() != std::io::ErrorKind::NotFound => return Err(error),
        _ => (),
    }
    let mut temp = tempfile::NamedTempFile::new_in(root)?;
    temp.write_all(&bytes)?;
    temp.as_file().sync_all()?;
    temp.persist(root.join(RECORD)).map_err(|error| error.error)?;
    Ok(matches(root, stamp.stamp()).as_ref() == Some(&bytes))
}

#[cfg(test)]
#[path = "installed_outputs/tests.rs"]
mod tests;
