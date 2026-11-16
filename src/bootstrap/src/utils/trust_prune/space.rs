// Trust: space observations share the native cleanup plan, never its authority.

use std::collections::BTreeMap;
#[cfg(any(target_os = "macos", target_os = "linux"))]
use std::ffi::CStr;
use std::ffi::{CString, OsStr, OsString};
use std::fs::{File, Metadata};
use std::io;
#[cfg(any(target_os = "macos", target_os = "linux"))]
use std::os::fd::IntoRawFd;
use std::os::fd::{AsFd, AsRawFd, BorrowedFd, FromRawFd};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::MetadataExt;
use std::path::{Component, Path, PathBuf};

use serde_derive::Serialize;

/// Complete selected file allocation observed BEFORE selected deletion. This
/// is a checked snapshot, not an attribution of subsequent volume space gained.
#[derive(Debug, Serialize)]
pub struct Estimate {
    pub allocated_upper_bytes: u64,
    /// Unshared APFS file allocation; unavailable elsewhere or if any counted
    /// file's private-size observation could not be established.
    pub private_lower_bytes: Option<u64>,
    pub counted_inodes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Snapshot {
    device: u64,
    inode: u64,
    mode: u32,
    uid: u32,
    gid: u32,
    links: u64,
    length: u64,
    blocks: u64,
    modified: (i64, i64),
    changed: (i64, i64),
}
impl Snapshot {
    pub(crate) fn metadata(meta: &Metadata) -> Self {
        Self {
            device: meta.dev(),
            inode: meta.ino(),
            mode: meta.mode(),
            uid: meta.uid(),
            gid: meta.gid(),
            links: meta.nlink(),
            length: meta.len(),
            blocks: meta.blocks(),
            modified: (meta.mtime(), meta.mtime_nsec()),
            changed: (meta.ctime(), meta.ctime_nsec()),
        }
    }
    pub(crate) fn directory(&self) -> bool {
        self.mode & mode_bits(libc::S_IFMT) == mode_bits(libc::S_IFDIR)
    }
    #[cfg(any(target_os = "macos", feature = "native-cache-exec", test))]
    pub(crate) fn regular(&self) -> bool {
        self.mode & mode_bits(libc::S_IFMT) == mode_bits(libc::S_IFREG)
    }
    #[cfg(any(feature = "native-cache-exec", test))]
    pub(crate) fn symlink(&self) -> bool {
        self.mode & mode_bits(libc::S_IFMT) == mode_bits(libc::S_IFLNK)
    }
    #[cfg(any(feature = "native-cache-exec", test))]
    pub(crate) fn identity(&self) -> (u64, u64) {
        (self.device, self.inode)
    }
    #[cfg(any(feature = "native-cache-exec", test))]
    pub(crate) fn modified(&self) -> (i64, i64) {
        self.modified
    }
    #[cfg(any(feature = "native-cache-exec", test))]
    pub(crate) fn same_directory(&self, current: &Self) -> bool {
        self.directory()
            && current.directory()
            && self.identity() == current.identity()
            && self.mode == current.mode
            && self.uid == current.uid
            && self.gid == current.gid
    }
    #[cfg(any(feature = "native-cache-exec", test))]
    pub(crate) fn after_our_unlinks(&self, current: &Self, removed: u64) -> bool {
        self.identity() == current.identity()
            && self.mode == current.mode
            && self.uid == current.uid
            && self.gid == current.gid
            && self.length == current.length
            && self.blocks == current.blocks
            && self.modified == current.modified
            && self.links.checked_sub(removed) == Some(current.links)
            && (removed > 0 || self.changed == current.changed)
    }
    #[cfg(any(feature = "native-cache-exec", test))]
    pub(crate) fn links(&self) -> u64 {
        self.links
    }
    #[cfg(any(feature = "native-cache-exec", test))]
    pub(crate) fn allocated_blocks(&self) -> io::Result<u64> {
        self.blocks.checked_mul(512).ok_or_else(|| invalid("allocation overflow"))
    }
    pub(crate) fn allocated(&self) -> io::Result<u64> {
        let bytes = self.blocks.checked_mul(512).ok_or_else(|| invalid("allocation overflow"))?;
        Ok(if bytes == 0 { self.length } else { bytes })
    }
}

struct Inode {
    original: Snapshot,
    selected: u64,
    allocated: u64,
    private: Option<u64>,
}


/// Observation-only anchor to the SAME originally held output directory. All
/// selected paths are relative to it, with every intermediate component opened
/// no-follow. No file or directory description here acquires a cleanup lease.
pub(crate) struct Accounting {
    root: PathBuf,
    directory: File,
    paths: BTreeMap<PathBuf, Snapshot>,
    inodes: BTreeMap<(u64, u64), Inode>,
    #[cfg(test)]
    observer: Option<Observer>,
}
#[cfg(test)]
type Observer = Box<dyn FnMut(&Path, Point)>;
#[cfg(test)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum Point {
    OpenedDirectory,
    ListedDirectory,
    ObservedLeaf,
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
fn mode_bits(value: impl Into<u32>) -> u32 {
    value.into()
}
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn nonnegative(value: impl TryInto<u64>) -> io::Result<u64> {
    value.try_into().map_err(|_| invalid("negative observation field"))
}
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn time_piece(value: impl Into<i64>) -> i64 {
    value.into()
}
fn name(value: &OsStr) -> io::Result<CString> {
    CString::new(value.as_bytes()).map_err(|_| invalid("invalid observation name"))
}
pub(crate) fn open_at(parent: BorrowedFd<'_>, value: &OsStr, directory: bool) -> io::Result<File> {
    let value = name(value)?;
    let flags = libc::O_RDONLY
        | libc::O_NOFOLLOW
        | libc::O_NONBLOCK
        | libc::O_CLOEXEC
        | if directory { libc::O_DIRECTORY } else { 0 };
    // SAFETY: parent is borrowed for this call, value is terminated, and this
    // creates one independent, owned no-follow description. No original OFD's
    // cursor, descriptor flags or locking state is changed.
    let raw = unsafe { libc::openat(parent.as_raw_fd(), value.as_ptr(), flags) };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { File::from_raw_fd(raw) })
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn entry_at(parent: BorrowedFd<'_>, value: &OsStr, flags: libc::c_int) -> io::Result<Snapshot> {
    let value = name(value)?;
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: one relative leaf, original held parent, no symlink following,
    // and correctly sized output. A FIFO is only observed, never opened here.
    if unsafe { libc::fstatat(parent.as_raw_fd(), value.as_ptr(), stat.as_mut_ptr(), flags) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let stat = unsafe { stat.assume_init() };
    let (modified, changed) = (
        (time_piece(stat.st_mtime), time_piece(stat.st_mtime_nsec)),
        (time_piece(stat.st_ctime), time_piece(stat.st_ctime_nsec)),
    );
    #[cfg(target_os = "macos")]
    let device = stat.st_dev as u64; // Same signed dev_t conversion as MetadataExt::dev.
    #[cfg(target_os = "linux")]
    let device = nonnegative(stat.st_dev)?;
    Ok(Snapshot {
        device,
        inode: nonnegative(stat.st_ino)?,
        mode: mode_bits(stat.st_mode),
        uid: stat.st_uid,
        gid: stat.st_gid,
        links: nonnegative(stat.st_nlink)?,
        length: nonnegative(stat.st_size)?,
        blocks: nonnegative(stat.st_blocks)?,
        modified,
        changed,
    })
}
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn entry_at(_: BorrowedFd<'_>, _: &OsStr, _: libc::c_int) -> io::Result<Snapshot> {
    Err(io::ErrorKind::Unsupported.into())
}
pub(crate) fn metadata_at(parent: BorrowedFd<'_>, value: &OsStr) -> io::Result<Snapshot> {
    entry_at(parent, value, libc::AT_SYMLINK_NOFOLLOW)
}
#[cfg(any(feature = "native-cache-exec", test))]
pub(crate) fn followed_metadata_at(parent: BorrowedFd<'_>, value: &OsStr) -> io::Result<Snapshot> {
    entry_at(parent, value, 0)
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) fn entries(directory: BorrowedFd<'_>) -> io::Result<Vec<OsString>> {
    // dup+rewinddir would mutate the original directory's shared cursor. Open
    // "." relative to it instead, for a genuinely independent enumeration OFD.
    let independent = open_at(directory, OsStr::new("."), true)?;
    let raw = independent.as_raw_fd();
    let stream = unsafe { libc::fdopendir(raw) };
    if stream.is_null() {
        return Err(io::Error::last_os_error());
    }
    let _ = independent.into_raw_fd(); // DIR now owns this exact descriptor.
    struct Stream(*mut libc::DIR);
    impl Drop for Stream {
        fn drop(&mut self) {
            unsafe {
                libc::closedir(self.0);
            }
        }
    }
    let stream = Stream(stream);
    let mut result = Vec::new();
    loop {
        #[cfg(target_os = "macos")]
        let errno = unsafe { libc::__error() };
        #[cfg(target_os = "linux")]
        let errno = unsafe { libc::__errno_location() };
        unsafe {
            *errno = 0;
        }
        let entry = unsafe { libc::readdir(stream.0) };
        let error = unsafe { *errno };
        if entry.is_null() {
            if error != 0 {
                return Err(io::Error::from_raw_os_error(error));
            }
            break;
        }
        // SAFETY: copy this entry's live terminated name before the next call.
        let bytes = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
        if bytes == b"." || bytes == b".." {
            continue;
        }
        if bytes.is_empty() || bytes.contains(&b'/') {
            return Err(invalid("invalid directory entry"));
        }
        result.push(OsString::from_vec(bytes.to_vec()));
    }
    result.sort();
    Ok(result)
}
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn entries(_: BorrowedFd<'_>) -> io::Result<Vec<OsString>> {
    Err(io::ErrorKind::Unsupported.into())
}

impl Accounting {
    #[cfg(any(feature = "native-cache-exec", test))]
    pub(crate) fn root(&self) -> &Path {
        &self.root
    }
    pub(crate) fn new(root: &Path, directory: BorrowedFd<'_>) -> io::Result<Self> {
        Ok(Self {
            root: root.to_owned(),
            directory: open_at(directory, OsStr::new("."), true)?,
            paths: BTreeMap::new(),
            inodes: BTreeMap::new(),
            #[cfg(test)]
            observer: None,
        })
    }
    pub(crate) fn collect(&mut self, paths: &[PathBuf]) -> io::Result<()> {
        for path in paths {
            let relative = path
                .strip_prefix(&self.root)
                .map_err(|_| invalid("observation is outside original output"))?;
            let (parent, leaf) = self.parent(relative)?;
            self.visit(parent.as_fd(), &leaf, relative)?;
        }
        Ok(())
    }
    pub(crate) fn parent(&self, relative: &Path) -> io::Result<(File, OsString)> {
        let components = relative
            .components()
            .map(|part| match part {
                Component::Normal(part) => Ok(part),
                _ => Err(invalid("observation has a non-relative component")),
            })
            .collect::<io::Result<Vec<_>>>()?;
        let mut directory = open_at(self.directory.as_fd(), OsStr::new("."), true)?;
        let Some((leaf, parents)) = components.split_last() else {
            return Ok((directory, ".".into()));
        };
        for part in parents {
            directory = open_at(directory.as_fd(), part, true)?;
        }
        Ok((directory, (*leaf).to_owned()))
    }
    fn visit(&mut self, parent: BorrowedFd<'_>, leaf: &OsStr, relative: &Path) -> io::Result<()> {
        if self.paths.contains_key(relative) {
            return Ok(());
        }
        let before = metadata_at(parent, leaf)?;
        self.paths.insert(relative.to_owned(), before.clone());
        if before.directory() {
            let directory = open_at(parent, leaf, true)?;
            if Snapshot::metadata(&directory.metadata()?) != before {
                return Err(invalid("cleanup space inventory directory changed"));
            }
            #[cfg(test)]
            if let Some(observe) = &mut self.observer {
                observe(relative, Point::OpenedDirectory);
            }
            for entry in entries(directory.as_fd())? {
                self.visit(directory.as_fd(), &entry, &relative.join(&entry))?;
            }
            #[cfg(test)]
            if let Some(observe) = &mut self.observer {
                observe(relative, Point::ListedDirectory);
            }
            if metadata_at(parent, leaf)? != before
                || Snapshot::metadata(&directory.metadata()?) != before
            {
                return Err(invalid("cleanup space inventory directory changed"));
            }
            return Ok(());
        }
        #[cfg(test)]
        if let Some(observe) = &mut self.observer {
            observe(relative, Point::ObservedLeaf);
        }
        let allocated = before.allocated()?;
        let key = (before.device, before.inode);
        if let Some(inode) = self.inodes.get_mut(&key) {
            // All selected links are inventoried BEFORE our first deletion.
            // A changed count or any changed inode stamp invalidates the census.
            if inode.original != before {
                return Err(invalid("cleanup space inventory file or link census changed"));
            }
            inode.selected =
                inode.selected.checked_add(1).ok_or_else(|| invalid("link overflow"))?;
        } else {
            let private = private_size(parent, leaf, &before).map(|bytes| bytes.min(allocated));
            self.inodes.insert(key, Inode { original: before, selected: 1, allocated, private });
        }
        Ok(())
    }
    pub(crate) fn validate(&self) -> io::Result<()> {
        // Recheck every original selected name through the anchored namespace.
        // This also detects delete-a/add-outside even if its nlink is unchanged.
        for (relative, original) in &self.paths {
            let (parent, leaf) = self.parent(relative)?;
            if metadata_at(parent.as_fd(), &leaf)? != *original {
                return Err(invalid("cleanup space inventory selected path changed"));
            }
        }
        Ok(())
    }
    #[cfg(any(feature = "native-cache-exec", test))]
    pub(crate) fn identities(&self) -> std::collections::BTreeSet<(u64, u64)> {
        self.paths.values().map(Snapshot::identity).collect()
    }
    #[cfg(any(feature = "native-cache-exec", test))]
    pub(crate) fn original(&self, relative: &Path) -> Option<&Snapshot> {
        self.paths.get(relative)
    }
    pub(crate) fn finish(&self) -> io::Result<Estimate> {
        self.validate()?;
        let mut result = Estimate {
            allocated_upper_bytes: 0,
            private_lower_bytes: if cfg!(target_os = "macos") { Some(0_u64) } else { None },
            counted_inodes: 0,
        };
        for inode in self.inodes.values() {
            if inode.selected < inode.original.links {
                continue;
            }
            if inode.selected != inode.original.links || inode.original.links == 0 {
                return Err(invalid("cleanup space inventory link census changed"));
            }
            result.counted_inodes += 1;
            result.allocated_upper_bytes = result
                .allocated_upper_bytes
                .checked_add(inode.allocated)
                .ok_or_else(|| invalid("allocation overflow"))?;
            result.private_lower_bytes = match (result.private_lower_bytes, inode.private) {
                (Some(total), Some(bytes)) => Some(
                    total
                        .checked_add(bytes)
                        .ok_or_else(|| invalid("private allocation overflow"))?,
                ),
                _ => None,
            };
        }
        Ok(result)
    }
}

#[cfg(target_os = "macos")]
fn private_size(parent: BorrowedFd<'_>, leaf: &OsStr, before: &Snapshot) -> Option<u64> {
    if !before.regular() {
        return None;
    }
    let file = open_at(parent, leaf, false).ok()?;
    if Snapshot::metadata(&file.metadata().ok()?) != *before {
        return None;
    }
    let mut request = libc::attrlist {
        bitmapcount: libc::ATTR_BIT_MAP_COUNT,
        reserved: 0,
        commonattr: 0,
        volattr: 0,
        dirattr: 0,
        fileattr: 0,
        forkattr: libc::ATTR_CMNEXT_PRIVATESIZE,
    };
    let mut reply = [0_u8; 16];
    // SAFETY: bounded initialized buffer for one native off_t; same held file.
    if unsafe {
        libc::fgetattrlist(
            file.as_raw_fd(),
            (&raw mut request).cast(),
            reply.as_mut_ptr().cast(),
            reply.len(),
            libc::FSOPT_ATTR_CMN_EXTENDED,
        )
    } != 0
    {
        return None;
    }
    let length = u32::from_ne_bytes(reply[..4].try_into().ok()?) as usize;
    if !(12..=reply.len()).contains(&length)
        || Snapshot::metadata(&file.metadata().ok()?) != *before
        || metadata_at(parent, leaf).ok()? != *before
    {
        return None;
    }
    u64::try_from(i64::from_ne_bytes(reply[4..12].try_into().ok()?)).ok()
}
#[cfg(not(target_os = "macos"))]
fn private_size(_: BorrowedFd<'_>, _: &OsStr, _: &Snapshot) -> Option<u64> {
    None
}

/// Two observations of the SAME held build directory's volume. Other jobs
/// can change this volume, so their difference is not attributed to cleanup.
#[derive(Debug, Serialize)]
pub struct VolumeChange {
    pub available_before_bytes: u64,
    pub available_after_bytes: u64,
}

pub(crate) struct VolumeBefore {
    directory: File,
    available: u64,
}

impl VolumeBefore {
    pub(crate) fn capture(original: BorrowedFd<'_>) -> io::Result<Self> {
        let directory = open_at(original, OsStr::new("."), true)?;
        let available = available(&directory)?;
        Ok(Self { directory, available })
    }

    pub(crate) fn finish(self) -> io::Result<VolumeChange> {
        Ok(VolumeChange {
            available_before_bytes: self.available,
            available_after_bytes: available(&self.directory)?,
        })
    }
}

fn available(directory: &File) -> io::Result<u64> {
    let mut reply = std::mem::MaybeUninit::<libc::statvfs>::uninit();
    // SAFETY: fstatvfs initializes the complete correctly sized object on zero.
    if unsafe { libc::fstatvfs(directory.as_raw_fd(), reply.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let reply = unsafe { reply.assume_init() };
    fn nonnegative(value: impl TryInto<u64>) -> io::Result<u64> {
        value.try_into().map_err(|_| invalid("negative available space"))
    }
    nonnegative(reply.f_bavail)?
        .checked_mul(nonnegative(reply.f_frsize)?)
        .ok_or_else(|| invalid("available space overflow"))
}

#[cfg(test)]
mod tests;
