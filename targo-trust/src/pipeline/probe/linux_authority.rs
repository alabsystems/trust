//! Root authority for positive and negative loader lookups. Every component,
//! including the nearest existing parent of a missing target, is checked.
//! Symlinks are followed explicitly and their own and target chains retained.
//! Opened O_PATH descriptors bind metadata; root, ACL and namespace mutation
//! remain the stated host TCB, rather than an unclaimed atomic exec guarantee.

use std::collections::{BTreeMap, VecDeque};
use std::fs::OpenOptions;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Component, Path, PathBuf};

use super::{AuthorityKind, AuthorityNode, PathAuthority, SearchDirectoryEntry};

pub(super) fn validate_node(node: &AuthorityNode) -> Result<(), String> {
    if (node.path != "/" && !super::normalized_path(&node.path))
        || node.uid != 0
        || node.mode & !0o7777 != 0
        || node.inode == 0
    {
        return Err("GNU resolution source is not bounded root filesystem authority".into());
    }
    match (&node.kind, &node.link) {
        (AuthorityKind::Symlink, Some(link))
            if !link.is_empty() && link.len() <= 4096 && !link.chars().any(char::is_control) => {}
        (AuthorityKind::Directory | AuthorityKind::Object, None) if node.mode & 0o022 == 0 => {}
        _ => return Err("GNU resolution source is writable or has an invalid node kind".into()),
    }
    Ok(())
}

fn parts(path: &Path) -> Result<VecDeque<String>, String> {
    if !path.is_absolute() || path.to_str().is_none_or(|s| s.len() > 4096) {
        return Err("GNU symlink resolution is not a bounded absolute UTF-8 path".into());
    }
    path.components()
        .filter_map(|part| match part {
            Component::Normal(part) => Some(
                part.to_str()
                    .map(str::to_owned)
                    .ok_or_else(|| "GNU authority path is not UTF-8".to_owned()),
            ),
            Component::ParentDir => Some(Ok("..".to_owned())),
            _ => None,
        })
        .collect()
}

pub(super) fn resolve<F>(
    path: &str,
    kind: AuthorityKind,
    read: &mut F,
) -> Result<PathAuthority, String>
where
    F: FnMut(&Path) -> Result<Option<AuthorityNode>, String>,
{
    if !super::normalized_path(path) || kind == AuthorityKind::Symlink {
        return Err("GNU resolution request has an invalid path or role".into());
    }
    let mut pending = parts(Path::new(path))?;
    let mut current = PathBuf::from("/");
    let mut nodes = BTreeMap::new();
    let mut hops = 0;
    loop {
        let named = current.to_str().ok_or("GNU authority component is not UTF-8")?.to_owned();
        let Some(node) = read(&current)? else {
            if named == "/" {
                return Err("GNU resolution root is absent".into());
            }
            for part in pending {
                if part == ".." {
                    return Err("GNU missing symlink target has unresolved parent traversal".into());
                }
                current.push(part);
            }
            return Ok(PathAuthority {
                path: path.to_owned(),
                kind,
                target: current.to_str().ok_or("GNU missing target is not UTF-8")?.to_owned(),
                present: false,
                nodes: nodes.into_values().collect(),
            });
        };
        validate_node(&node)?;
        if node.path != named {
            return Err("GNU opened authority node has a different name".into());
        }
        if let Some(previous) = nodes.insert(named, node.clone()) {
            if previous != node {
                return Err("GNU authority changed while resolving a target".into());
            }
        }
        if nodes.len() > super::search::MAX_NODES {
            return Err("GNU authority component count exceeds the bound".into());
        }
        if node.kind == AuthorityKind::Symlink {
            hops += 1;
            if hops > 40 {
                return Err("GNU authority symlink count exceeds the bound".into());
            }
            let link = Path::new(node.link.as_deref().ok_or("GNU symlink target is absent")?);
            let mut target = if link.is_absolute() {
                link.to_owned()
            } else {
                current.parent().ok_or("GNU root cannot be a symlink")?.join(link)
            };
            for part in pending {
                target.push(part);
            }
            // Keep parent traversals until their preceding component has been
            // resolved. Lexically collapsing a/../b before following a symlink
            // at a would inspect a different path from the kernel.
            pending = parts(&target)?;
            current = PathBuf::from("/");
        } else if let Some(part) = pending.pop_front() {
            if node.kind != AuthorityKind::Directory {
                return Err("GNU resolution ancestor is not a directory".into());
            }
            if part == ".." {
                if current != Path::new("/") {
                    current.pop();
                }
            } else {
                current.push(part);
            }
        } else {
            if node.kind != kind {
                return Err("GNU resolution target has the wrong file/directory role".into());
            }
            return Ok(PathAuthority {
                path: path.to_owned(),
                kind,
                target: current.to_str().ok_or("GNU target is not UTF-8")?.to_owned(),
                present: true,
                nodes: nodes.into_values().collect(),
            });
        }
    }
}

fn identity(metadata: &std::fs::Metadata) -> (u64, u64, u32, u32, u32, u64, i64, i64) {
    (
        metadata.dev(),
        metadata.ino(),
        metadata.mode(),
        metadata.uid(),
        metadata.gid(),
        metadata.len(),
        metadata.ctime(),
        metadata.ctime_nsec(),
    )
}

fn read_node(path: &Path) -> Result<Option<AuthorityNode>, String> {
    let before = match std::fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(format!("GNU resolution authority {}: {error}", path.display())),
    };
    // O_PATH inspects a symlink inode itself with O_NOFOLLOW, and never opens a
    // device for I/O. Every regular file and directory is bound the same way.
    let opened = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_PATH | libc::O_NOFOLLOW)
        .open(path)
        .map_err(|error| format!("GNU opened authority {}: {error}", path.display()))?;
    let kind = before.file_type();
    let (kind, link) = if kind.is_symlink() {
        let link = std::fs::read_link(path).map_err(|error| error.to_string())?;
        (
            AuthorityKind::Symlink,
            Some(link.to_str().ok_or("GNU authority symlink is not UTF-8")?.to_owned()),
        )
    } else if kind.is_dir() {
        (AuthorityKind::Directory, None)
    } else if kind.is_file() {
        (AuthorityKind::Object, None)
    } else {
        return Err("GNU resolution authority is not a directory, symlink or regular file".into());
    };
    if identity(&before) != identity(&opened.metadata().map_err(|error| error.to_string())?)
        || identity(&before)
            != identity(&std::fs::symlink_metadata(path).map_err(|error| error.to_string())?)
    {
        return Err("GNU named and opened authority changed during capture".into());
    }
    Ok(Some(AuthorityNode {
        path: path.to_str().ok_or("GNU authority name is not UTF-8")?.to_owned(),
        kind,
        device: before.dev(),
        inode: before.ino(),
        uid: before.uid(),
        gid: before.gid(),
        mode: before.mode() & 0o7777,
        link,
    }))
}

pub(super) fn observe(requests: &[(String, AuthorityKind)]) -> Result<Vec<PathAuthority>, String> {
    if requests.len() > super::search::MAX_PATHS {
        return Err("GNU authority request count exceeds its bound".into());
    }
    let mut seen = BTreeMap::new();
    let mut read = |path: &Path| {
        let node = read_node(path)?;
        let key = path.to_owned();
        if let Some(previous) = seen.insert(key, node.clone()) {
            if previous != node {
                return Err("GNU resolution authority changed across the inventory".into());
            }
        }
        if seen.len() > super::search::MAX_TOTAL_NODES {
            return Err("GNU unique authority observations exceed their bound".into());
        }
        Ok(node)
    };
    let mut total_nodes = 0usize;
    let mut total_text = 0usize;
    requests
        .iter()
        .map(|(path, kind)| {
            let observed = resolve(path, *kind, &mut read)?;
            account(&observed, &mut total_nodes, &mut total_text)?;
            Ok(observed)
        })
        .collect()
}

pub(super) fn account(
    path: &PathAuthority,
    nodes: &mut usize,
    text: &mut usize,
) -> Result<(), String> {
    *nodes = nodes
        .checked_add(path.nodes.len())
        .filter(|&n| n <= super::search::MAX_TOTAL_NODES)
        .ok_or("GNU authority component inventory exceeds its total bound")?;
    let size = path
        .nodes
        .iter()
        .map(|node| node.path.len() + node.link.as_ref().map_or(0, String::len))
        .try_fold(path.path.len() + path.target.len(), |sum, n| sum.checked_add(n))
        .ok_or("GNU authority text count overflow")?;
    *text = text
        .checked_add(size)
        .filter(|&n| n <= super::search::MAX_AUTHORITY_TEXT)
        .ok_or("GNU authority path text exceeds its total bound")?;
    Ok(())
}

pub(super) fn census(directories: &[String]) -> Result<Vec<SearchDirectoryEntry>, String> {
    // Validate all directory chains before enumerating any of their entries.
    let requests =
        directories.iter().map(|path| (path.clone(), AuthorityKind::Directory)).collect::<Vec<_>>();
    let authority = observe(&requests)?;
    let mut entries = BTreeMap::new();
    let mut scanned = 0usize;
    for directory in &authority {
        if !directory.present {
            continue;
        }
        let children = std::fs::read_dir(&directory.path)
            .map_err(|error| format!("GNU default-directory census: {error}"))?;
        for child in children {
            scanned += 1;
            if scanned > super::search::MAX_PATHS {
                return Err("GNU directory enumeration exceeds its entry bound".into());
            }
            let child = child.map_err(|error| error.to_string())?;
            let name = child
                .file_name()
                .into_string()
                .map_err(|_| "GNU search directory has a non-UTF-8 entry")?;
            if !super::super::linux_elf::valid_soname(&name) {
                continue;
            }
            let kind = match std::fs::metadata(child.path()) {
                Ok(metadata) if metadata.is_file() => AuthorityKind::Object,
                Ok(metadata) if metadata.is_dir() => AuthorityKind::Directory,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => AuthorityKind::Object,
                _ => return Err("GNU search directory has a non-file runtime lookup target".into()),
            };
            entries.insert(
                (directory.path.clone(), name.clone()),
                SearchDirectoryEntry { directory: directory.path.clone(), name, kind },
            );
            if entries.len() > 16_384 {
                return Err("GNU search directory entry census exceeds its bound".into());
            }
        }
    }
    Ok(entries.into_values().collect())
}

#[cfg(test)]
#[path = "linux_authority_tests.rs"]
mod tests;
