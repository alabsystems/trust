//! Observe every namespace component required by a kept symlink. The final
//! inode alone misses a deleted bridge or `selected/../kept` dependency.
//! All walks use held directory descriptions and no-follow relative lookups;
//! these observations create no ownership or permission to delete.

use std::collections::VecDeque;
use std::os::unix::ffi::OsStringExt as _;

use super::*;

const MAX_COMPONENTS: usize = 4096;
const MAX_SYMLINKS: usize = 40;
const MAX_LINK_BYTES: usize = 64 * 1024;

struct Named {
    parent: File,
    name: OsString,
    before: space::Snapshot,
}
fn read_link(parent: BorrowedFd<'_>, name: &OsStr) -> io::Result<OsString> {
    let name = cstring(name)?;
    let mut bytes = vec![0; MAX_LINK_BYTES];
    let count = unsafe {
        libc::readlinkat(parent.as_raw_fd(), name.as_ptr(), bytes.as_mut_ptr().cast(), bytes.len())
    };
    if count < 0 {
        return Err(io::Error::last_os_error());
    }
    let count = usize::try_from(count).map_err(|_| invalid("invalid kept symlink length"))?;
    if count == 0 || count == bytes.len() {
        return Err(invalid("empty or over-bound kept symlink target"));
    }
    bytes.truncate(count);
    Ok(OsString::from_vec(bytes))
}
fn components(path: &Path) -> io::Result<VecDeque<OsString>> {
    let mut result = VecDeque::new();
    for part in path.components() {
        if result.len() >= MAX_COMPONENTS {
            return Err(invalid("kept symlink target exceeds component bound"));
        }
        result.push_back(match part {
            Component::RootDir => OsString::from("/"),
            Component::CurDir => OsString::from("."),
            Component::ParentDir => OsString::from(".."),
            Component::Normal(name) => name.to_owned(),
            Component::Prefix(_) => return Err(invalid("foreign kept symlink path prefix")),
        });
    }
    Ok(result)
}

fn unchanged(before: &space::Snapshot, after: &space::Snapshot) -> bool {
    if before.directory() { before.same_directory(after) } else { before == after }
}
fn selected(meta: &space::Snapshot, doomed: &BTreeSet<(u64, u64)>) -> io::Result<()> {
    if doomed.contains(&meta.identity()) {
        Err(invalid("kept symlink traverses selected namespace"))
    } else {
        Ok(())
    }
}

pub(super) fn preserved_target(
    parent: BorrowedFd<'_>,
    name: &OsStr,
    doomed: &BTreeSet<(u64, u64)>,
) -> io::Result<(u64, u64)> {
    let mut directory = space::open_at(parent, OsStr::new("."), true)?;
    let mut pending = VecDeque::from([name.to_owned()]);
    let mut named = Vec::new();
    let mut directories = Vec::new();
    let mut links = 0;
    let mut steps = 0;
    let target = loop {
        steps += 1;
        if steps > MAX_COMPONENTS {
            return Err(invalid("kept symlink namespace exceeds bound"));
        }
        let current = space::Snapshot::metadata(&directory.metadata()?);
        selected(&current, doomed)?;
        let Some(name) = pending.pop_front() else {
            break current.identity();
        };
        if name == OsStr::new("/") {
            directory = space::open_at(directory.as_fd(), OsStr::new("/"), true)?;
            continue;
        }
        let before = space::metadata_at(directory.as_fd(), &name)?;
        // Check BEFORE following a symlink, entering a directory or processing
        // `..`. Kernel traversal needs each such inode even if it exits again.
        selected(&before, doomed)?;
        named.push(Named {
            parent: directory.try_clone()?,
            name: name.clone(),
            before: before.clone(),
        });
        if before.symlink() {
            links += 1;
            if links > MAX_SYMLINKS {
                return Err(invalid("kept symlink loop or excessive chain"));
            }
            let target = read_link(directory.as_fd(), &name)?;
            if space::metadata_at(directory.as_fd(), &name)? != before {
                return Err(invalid("kept symlink changed while reading target"));
            }
            let mut expanded = components(Path::new(&target))?;
            if expanded.len().saturating_add(pending.len()).saturating_add(steps) > MAX_COMPONENTS {
                return Err(invalid("kept symlink expansion exceeds component bound"));
            }
            expanded.append(&mut pending);
            pending = expanded;
            continue;
        }
        if !pending.is_empty() {
            if !before.directory() {
                return Err(io::ErrorKind::NotADirectory.into());
            }
            let next = space::open_at(directory.as_fd(), &name, true)?;
            if !unchanged(&before, &space::Snapshot::metadata(&next.metadata()?)) {
                return Err(invalid("kept symlink traversal directory changed"));
            }
            // Independent held descriptions; no shared cursor is changed.
            directories.push((next.try_clone()?, before));
            directory = next;
        } else {
            break before.identity();
        }
    };
    for entry in named {
        if !unchanged(&entry.before, &space::metadata_at(entry.parent.as_fd(), &entry.name)?) {
            return Err(invalid("kept symlink namespace changed during traversal"));
        }
    }
    for (directory, before) in directories {
        if !unchanged(&before, &space::Snapshot::metadata(&directory.metadata()?)) {
            return Err(invalid("kept symlink held traversal directory changed"));
        }
    }
    // Retain the kernel's own complete resolution as an independent bookend;
    // lexical path components never replace the actual followed observation.
    if space::followed_metadata_at(parent, name)?.identity() != target {
        return Err(invalid("kept symlink final target differs from held traversal"));
    }
    Ok(target)
}
