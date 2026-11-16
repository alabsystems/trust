use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File, OpenOptions};
use std::io::Read;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Component, Path, PathBuf};

use serde::{Deserialize, Serialize};
use trust_sha2::{Digest, Sha256};

use crate::{Result, refusal};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Fingerprint {
    device: u64,
    inode: u64,
    mode: u32,
    size: u64,
    modified_seconds: i64,
    modified_nanos: i64,
    changed_seconds: i64,
    changed_nanos: i64,
}

impl Fingerprint {
    pub(crate) fn of(m: &fs::Metadata) -> Self {
        Self {
            device: m.dev(),
            inode: m.ino(),
            mode: m.mode(),
            size: m.size(),
            modified_seconds: m.mtime(),
            modified_nanos: m.mtime_nsec(),
            changed_seconds: m.ctime(),
            changed_nanos: m.ctime_nsec(),
        }
    }
    pub(crate) fn inode(&self) -> (u64, u64) {
        (self.device, self.inode)
    }
}

pub(crate) fn path_bytes(path: &Path) -> Vec<u8> {
    path.as_os_str().as_bytes().to_vec()
}

pub(crate) fn no_link_ancestors(root: &Path, relative: &Path) -> Result<PathBuf> {
    let mut path = root.to_owned();
    let components = relative.components().collect::<Vec<_>>();
    for (index, component) in components.iter().enumerate() {
        let Component::Normal(name) = component else {
            return Err(refusal("noncanonical input path"));
        };
        path.push(name);
        if index + 1 < components.len() {
            let metadata = fs::symlink_metadata(&path)?;
            if !metadata.file_type().is_dir() {
                return Err(refusal(format!(
                    "input parent is not an exact directory: {}",
                    path.display()
                )));
            }
        }
    }
    Ok(path)
}

pub(crate) fn read_file(path: &Path) -> Result<Vec<u8>> {
    let before = fs::symlink_metadata(path)?;
    if !before.file_type().is_file() {
        return Err(refusal(format!("input is not an exact regular file: {}", path.display())));
    }
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
        .open(path)?;
    let stamp = Fingerprint::of(&before);
    if Fingerprint::of(&file.metadata()?) != stamp {
        return Err(refusal(format!("input changed before open: {}", path.display())));
    }
    let mut contents = Vec::new();
    file.read_to_end(&mut contents)?;
    if Fingerprint::of(&file.metadata()?) != stamp
        || Fingerprint::of(&fs::symlink_metadata(path)?) != stamp
    {
        return Err(refusal(format!("input changed while reading: {}", path.display())));
    }
    Ok(contents)
}

pub(crate) fn hash_file(path: &Path) -> Result<String> {
    let before = fs::symlink_metadata(path)?;
    if !before.file_type().is_file() {
        return Err(refusal(format!("input is not an exact regular file: {}", path.display())));
    }
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
        .open(path)?;
    let stamp = Fingerprint::of(&before);
    if Fingerprint::of(&file.metadata()?) != stamp {
        return Err(refusal(format!("input changed before hashing: {}", path.display())));
    }
    let digest = hash_open_file(&mut file)?;
    if Fingerprint::of(&file.metadata()?) != stamp
        || Fingerprint::of(&fs::symlink_metadata(path)?) != stamp
    {
        return Err(refusal(format!("input changed while hashing: {}", path.display())));
    }
    Ok(digest)
}

fn hash_open_file(file: &mut File) -> Result<String> {
    let mut digest = Sha256::new();
    let mut block = vec![0; 1024 * 1024];
    loop {
        let n = file.read(&mut block)?;
        if n == 0 {
            break;
        }
        digest.update(&block[..n]);
    }
    Ok(format!("{:x}", digest.finalize()))
}

pub(crate) fn hash_bytes(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

pub(crate) fn read_link(path: &Path) -> Result<PathBuf> {
    let before = fs::symlink_metadata(path)?;
    if !before.file_type().is_symlink() {
        return Err(refusal(format!("input is not an exact symlink: {}", path.display())));
    }
    let target = fs::read_link(path)?;
    if Fingerprint::of(&before) != Fingerprint::of(&fs::symlink_metadata(path)?) {
        return Err(refusal(format!("symlink changed: {}", path.display())));
    }
    Ok(target)
}

/// Stable pathname-byte inventory, never following directory links.
pub(crate) fn entries(root: &Path, omit_git: bool, omit_root: &[&str]) -> Result<Vec<PathBuf>> {
    let mut pending = vec![PathBuf::new()];
    let mut out = Vec::new();
    while let Some(relative) = pending.pop() {
        let directory = root.join(&relative);
        if !fs::symlink_metadata(&directory)?.file_type().is_dir() {
            return Err(refusal(format!("input directory changed: {}", directory.display())));
        }
        for entry in fs::read_dir(&directory)? {
            let entry = entry?;
            let name = entry.file_name();
            if (omit_git && name == ".git")
                || (relative.as_os_str().is_empty() && omit_root.iter().any(|n| name == *n))
            {
                continue;
            }
            let relative = relative.join(name);
            let metadata = fs::symlink_metadata(root.join(&relative))?;
            if metadata.file_type().is_dir() {
                pending.push(relative.clone());
            } else if !metadata.file_type().is_file() && !metadata.file_type().is_symlink() {
                return Err(refusal(format!(
                    "{} is neither a regular file, a symlink nor a directory",
                    root.join(&relative).display()
                )));
            }
            out.push(relative);
        }
    }
    out.sort_by_cached_key(|path| path_bytes(path));
    Ok(out)
}

pub(crate) type TreeStats = BTreeMap<Vec<u8>, Fingerprint>;

pub(crate) fn stats(root: &Path, omit_git: bool, omit_root: &[&str]) -> Result<TreeStats> {
    entries(root, omit_git, omit_root)?
        .into_iter()
        .map(|relative| {
            let path = root.join(&relative);
            let metadata = fs::symlink_metadata(&path)?;
            Ok((path_bytes(&relative), Fingerprint::of(&metadata)))
        })
        .collect()
}

pub(crate) fn closed_links(root: &Path, entries: &[PathBuf]) -> Result<BTreeMap<PathBuf, PathBuf>> {
    let files = entries
        .iter()
        .filter_map(|relative| {
            let path = root.join(relative);
            match fs::symlink_metadata(&path) {
                Ok(metadata) if metadata.file_type().is_file() => Some(Ok(path)),
                Ok(_) => None,
                Err(error) => Some(Err(error)),
            }
        })
        .collect::<std::io::Result<BTreeSet<_>>>()?;
    let mut resolved = BTreeMap::new();
    for relative in entries {
        let path = root.join(relative);
        if fs::symlink_metadata(&path)?.file_type().is_symlink() {
            let target = fs::canonicalize(&path)?;
            if !files.contains(&target) {
                return Err(refusal(format!(
                    "link escapes the fully bound regular-file closure: {}",
                    path.display()
                )));
            }
            let target = target
                .strip_prefix(root)
                .map_err(|_| refusal("resolved link escaped the bound root"))?
                .to_path_buf();
            resolved.insert(relative.clone(), target);
        }
    }
    Ok(resolved)
}
