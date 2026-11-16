use std::collections::BTreeMap;
use std::ffi::{CStr, CString};
use std::fs::{self, File, Metadata, OpenOptions};
use std::io::Read;
use std::os::fd::{AsRawFd, FromRawFd, IntoRawFd};
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};

use trust_sha2::{Digest, Sha256};

use super::{DirectorySnapshot, Entry, EntryKind, Limits};
use crate::files::stamp;
use crate::{Refusal, Result};

fn refused(reason: &str) -> Refusal {
    Refusal(format!("directory inventory: {reason}"))
}

pub(super) fn text(path: &Path, maximum: usize) -> Result<&str> {
    let text = path.to_str().ok_or_else(|| refused("path is not lossless UTF-8"))?;
    if text.len() > maximum || text.chars().any(char::is_control) {
        return Err(refused("path exceeds its byte bound or contains controls"));
    }
    Ok(text)
}

struct Directory(*mut libc::DIR);

impl Drop for Directory {
    fn drop(&mut self) {
        // SAFETY: fdopendir gave this object sole ownership of this stream.
        unsafe { libc::closedir(self.0) };
    }
}

fn open_at(parent: &File, name: &str, directory: bool) -> Result<File> {
    let name = CString::new(name).map_err(|_| refused("entry name contains NUL"))?;
    let mut kind = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: live parent handle and NUL-terminated component; stat is output.
    if unsafe {
        libc::fstatat(
            parent.as_raw_fd(),
            name.as_ptr(),
            kind.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } != 0
    {
        return Err(std::io::Error::last_os_error().into());
    }
    // SAFETY: successful fstatat initialized kind.
    let mode = unsafe { kind.assume_init() }.st_mode & libc::S_IFMT;
    if mode != libc::S_IFREG && mode != libc::S_IFDIR {
        return Err(refused("links and special entries are unsupported"));
    }
    let flags = libc::O_RDONLY
        | libc::O_NOFOLLOW
        | libc::O_NONBLOCK
        | libc::O_CLOEXEC
        | if directory { libc::O_DIRECTORY } else { 0 };
    // SAFETY: live parent and terminated component. Flags forbid following links.
    let fd = unsafe { libc::openat(parent.as_raw_fd(), name.as_ptr(), flags) };
    if fd < 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    // SAFETY: openat returned a new descriptor owned by this call.
    Ok(unsafe { File::from_raw_fd(fd) })
}

fn names(parent: &File, limits: Limits) -> Result<Vec<String>> {
    // Opening '.' gives a new directory offset; dup would share the original
    // offset and make later verification incorrectly start at end-of-directory.
    let cursor = open_at(parent, ".", true)?;
    let raw = cursor.into_raw_fd();
    // SAFETY: raw is a directory descriptor, transferred only on success.
    let pointer = unsafe { libc::fdopendir(raw) };
    if pointer.is_null() {
        let error = std::io::Error::last_os_error();
        // SAFETY: fdopendir failed and did not take descriptor ownership.
        unsafe { libc::close(raw) };
        return Err(error.into());
    }
    let directory = Directory(pointer);
    let mut output = Vec::new();
    loop {
        errno::set_errno(errno::Errno(0));
        // SAFETY: the stream is live and accessed by this thread only.
        let entry = unsafe { libc::readdir(directory.0) };
        if entry.is_null() {
            let error = errno::errno().0;
            if error != 0 {
                return Err(std::io::Error::from_raw_os_error(error).into());
            }
            break;
        }
        // SAFETY: readdir provides a NUL-terminated d_name until the next call.
        let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) }
            .to_str()
            .map_err(|_| refused("entry name is not lossless UTF-8"))?;
        if matches!(name, "." | "..") {
            continue;
        }
        if output.len() >= limits.max_entries {
            return Err(refused("entry count exceeds its bound"));
        }
        text(Path::new(name), limits.max_path_bytes)?;
        output.push(name.to_owned());
    }
    output.sort();
    if output.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(refused("duplicate entry names"));
    }
    Ok(output)
}

struct Capture {
    root: PathBuf,
    limits: Limits,
    entries: Vec<Entry>,
    observed: BTreeMap<PathBuf, Metadata>,
    total_bytes: u64,
    total_path_bytes: usize,
}

impl Capture {
    fn unchanged(&self, relative: &Path, file: &File, before: &Metadata) -> Result<()> {
        if stamp(before) != stamp(&file.metadata()?)
            || stamp(before) != stamp(&fs::symlink_metadata(self.root.join(relative))?)
        {
            return Err(refused("entry changed during capture"));
        }
        Ok(())
    }

    fn walk(
        &mut self,
        directory: &File,
        relative: &Path,
        depth: usize,
        verify: bool,
    ) -> Result<usize> {
        let before = directory.metadata()?;
        if !before.is_dir() {
            return Err(refused("directory changed kind"));
        }
        if verify {
            let expected = self.observed.get(relative).ok_or_else(|| refused("new directory"))?;
            if stamp(expected) != stamp(&before) {
                return Err(refused("directory changed before final verification"));
            }
        } else {
            self.observed.insert(relative.into(), before.clone());
        }
        self.unchanged(relative, directory, &before)?;
        let mut visited = 0usize;
        for name in names(directory, self.limits)? {
            let child = relative.join(&name);
            let path_bytes = text(&child, self.limits.max_path_bytes)?.len();
            text(&self.root.join(&child), self.limits.max_path_bytes)?;
            if depth >= self.limits.max_depth {
                return Err(refused("tree depth exceeds its bound"));
            }
            if !verify {
                if self.entries.len() >= self.limits.max_entries {
                    return Err(refused("entry count exceeds its bound"));
                }
                self.total_path_bytes = self
                    .total_path_bytes
                    .checked_add(path_bytes)
                    .ok_or_else(|| refused("path-byte count overflow"))?;
                if self.total_path_bytes > self.limits.max_total_path_bytes {
                    return Err(refused("aggregate path bytes exceed their bound"));
                }
            }
            let pathname = fs::symlink_metadata(self.root.join(&child))?;
            if !pathname.is_file() && !pathname.is_dir() {
                return Err(refused("links and special entries are unsupported"));
            }
            let mut file = open_at(directory, &name, pathname.is_dir())?;
            self.unchanged(&child, &file, &pathname)?;
            if verify {
                let expected = self.observed.get(&child).ok_or_else(|| refused("new entry"))?;
                if stamp(expected) != stamp(&pathname) {
                    return Err(refused("entry changed before final verification"));
                }
            } else {
                self.observed.insert(child.clone(), pathname.clone());
                let kind = if pathname.is_dir() {
                    EntryKind::Directory
                } else {
                    if pathname.len() > self.limits.max_file_bytes {
                        return Err(refused("file bytes exceed their bound"));
                    }
                    self.total_bytes = self
                        .total_bytes
                        .checked_add(pathname.len())
                        .ok_or_else(|| refused("file-byte count overflow"))?;
                    if self.total_bytes > self.limits.max_total_bytes {
                        return Err(refused("aggregate file bytes exceed their bound"));
                    }
                    let mut hash = Sha256::new();
                    let mut read = 0u64;
                    let mut buffer = vec![0u8; 64 * 1024];
                    loop {
                        let n = file.read(&mut buffer)?;
                        if n == 0 {
                            break;
                        }
                        read = read
                            .checked_add(n as u64)
                            .ok_or_else(|| refused("file-byte count overflow"))?;
                        if read > pathname.len() || read > self.limits.max_file_bytes {
                            return Err(refused("file grew while hashing"));
                        }
                        hash.update(&buffer[..n]);
                    }
                    if read != pathname.len() {
                        return Err(refused("file shortened while hashing"));
                    }
                    self.unchanged(&child, &file, &pathname)?;
                    EntryKind::File { bytes: read, sha256: format!("{:x}", hash.finalize()) }
                };
                self.entries.push(Entry { relative_path: child.clone(), kind });
            }
            visited += 1;
            if pathname.is_dir() {
                visited += self.walk(&file, &child, depth + 1, verify)?;
            }
            self.unchanged(&child, &file, &pathname)?;
        }
        self.unchanged(relative, directory, &before)?;
        Ok(visited)
    }
}

pub(super) fn capture(root: &Path, limits: Limits) -> Result<DirectorySnapshot> {
    capture_with_verification_hook(root, limits, || {})
}

pub(super) fn capture_with_verification_hook(
    root: &Path,
    limits: Limits,
    before_verification: impl FnOnce(),
) -> Result<DirectorySnapshot> {
    if !root.is_absolute() {
        return Err(refused("root must be absolute"));
    }
    let root = fs::canonicalize(root)?;
    text(&root, limits.max_path_bytes)?;
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
        .open(&root)?;
    let mut capture = Capture {
        root,
        limits,
        entries: Vec::new(),
        observed: BTreeMap::new(),
        total_bytes: 0,
        total_path_bytes: 0,
    };
    capture.walk(&file, Path::new(""), 0, false)?;
    before_verification();
    // A complete second pass catches earlier siblings changed while a later
    // subtree was read. It does not turn observations into an atomic snapshot.
    let checked = capture.walk(&file, Path::new(""), 0, true)?;
    if checked != capture.entries.len() {
        return Err(refused("entries disappeared before final verification"));
    }
    capture.entries.sort_by(|a, b| a.relative_path.cmp(&b.relative_path));
    Ok(DirectorySnapshot {
        root: capture.root,
        entries: capture.entries,
        total_bytes: capture.total_bytes,
    })
}
