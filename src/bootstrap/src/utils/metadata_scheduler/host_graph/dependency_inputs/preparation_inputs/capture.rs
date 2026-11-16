//! Readonly producers from an already owned original source. These private
//! file guards create no Root, materialization, parser or closure authority.
use std::ffi::CString;
use std::fs::Metadata;
use std::os::fd::{AsFd as _, AsRawFd as _, BorrowedFd, FromRawFd};
use std::os::unix::fs::{FileExt as _, MetadataExt as _};

use trust_resource_controller::bootstrap_graph::configuration::{self, Timestamp};
use trust_resource_controller::bootstrap_graph::{ConfigurationAttachment, transport};

use super::*;

#[derive(PartialEq, Eq)]
struct Stamp {
    device: u64,
    inode: u64,
    mode: u32,
    uid: u32,
    gid: u32,
    links: u64,
    bytes: u64,
    modified: (i64, i64),
    changed: (i64, i64),
}
impl From<Metadata> for Stamp {
    fn from(m: Metadata) -> Self {
        Self {
            device: m.dev(),
            inode: m.ino(),
            mode: m.mode(),
            uid: m.uid(),
            gid: m.gid(),
            links: m.nlink(),
            bytes: m.len(),
            modified: (m.mtime(), m.mtime_nsec()),
            changed: (m.ctime(), m.ctime_nsec()),
        }
    }
}
#[derive(Default)]
struct Partial {
    root: Option<Stamp>,
    pending: Vec<File>,
    parents: Vec<(File, Stamp)>,
    file: Option<(File, Stamp)>,
    request: Option<ConfigurationAttachment>,
    contents: Option<String>,
    offered: bool,
}
pub(super) struct SelectedFile {
    source: Arc<OriginalSourceRoot>,
    relative: Vec<u8>,
    end: Instant,
    partial: Mutex<Partial>,
}
pub(super) struct Offer {
    original: Arc<SelectedFile>,
    description: File,
    pub(super) request: ConfigurationAttachment,
}
fn opened(parent: BorrowedFd<'_>, name: &[u8], directory: bool) -> io::Result<File> {
    let name = CString::new(name).map_err(io::Error::other)?;
    // No search, symlink following, cursor/flag changes or alternate root.
    let flags = libc::O_RDONLY
        | libc::O_NOFOLLOW
        | libc::O_NONBLOCK
        | libc::O_CLOEXEC
        | if directory { libc::O_DIRECTORY } else { 0 };
    let fd = unsafe { libc::openat(parent.as_raw_fd(), name.as_ptr(), flags) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { File::from_raw_fd(fd) })
}
impl SelectedFile {
    pub(super) fn pending(
        source: Arc<OriginalSourceRoot>,
        relative: Vec<u8>,
        end: Instant,
    ) -> Self {
        Self { source, relative, end, partial: Mutex::new(Partial::default()) }
    }
    pub(super) fn relative(&self) -> &[u8] {
        &self.relative
    }
    pub(super) fn capture(
        &self,
        key: &Key,
        sequence: u64,
        reserve: impl FnOnce(u64) -> io::Result<()>,
    ) -> io::Result<()> {
        time(self.end)?;
        self.source.check_current()?;
        let mut part = lock(&self.partial, self.end)?;
        if part.root.is_some() || part.file.is_some() {
            return Err(io::Error::other("configuration capture is one-use"));
        }
        part.root = Some(self.source.metadata()?.into());
        let names: Vec<_> = self.relative.split(|b| *b == b'/').collect();
        for name in &names[..names.len() - 1] {
            time(self.end)?;
            let parent =
                part.parents.last().map_or(self.source.directory()?, |(file, _)| file.as_fd());
            let file = opened(parent, name, true)?;
            part.pending.push(file);
            let file = part.pending.last().unwrap();
            trust_resource_provenance::require_no_acl_grants(file)?;
            let stamp = file.metadata()?.into();
            let file = part.pending.pop().unwrap();
            part.parents.push((file, stamp));
        }
        let parent = part.parents.last().map_or(self.source.directory()?, |(file, _)| file.as_fd());
        let file = opened(
            parent,
            names.last().ok_or_else(|| io::Error::other("empty configuration selector"))?,
            false,
        )?;
        part.pending.push(file);
        let file = part.pending.last().unwrap();
        trust_resource_provenance::require_no_acl_grants(file)?;
        let stamp: Stamp = file.metadata()?.into();
        let bytes = stamp.bytes;
        // Keep the actual file in this already-retained partial issuer BEFORE
        // regular-file/size checks, allocation, reads, decoding or callbacks.
        let file = part.pending.pop().unwrap();
        part.file = Some((file, stamp));
        let (file, stamp) = part.file.as_ref().unwrap();
        if stamp.mode & libc::S_IFMT as u32 != libc::S_IFREG as u32
            || bytes > configuration::MAX_BYTES
        {
            return Err(io::Error::other("configuration is not a bounded regular file"));
        }
        reserve(bytes)?; // permanent declaration charge BEFORE content allocation/read
        let mut contents = vec![0; bytes as usize];
        file.read_exact_at(&mut contents, 0)?;
        time(self.end)?;
        let remaining =
            self.end.checked_duration_since(Instant::now()).ok_or(io::ErrorKind::TimedOut)?;
        let request = ConfigurationAttachment {
            key: key.clone(),
            sequence,
            relative: self.relative.clone(),
            file: FileIdentity { device: stamp.device, inode: stamp.inode },
            bytes,
            sha256: Sha256::digest(&contents).into(),
            modified: Timestamp {
                seconds: stamp.modified.0,
                nanoseconds: stamp.modified.1.try_into().map_err(io::Error::other)?,
            },
            changed: Timestamp {
                seconds: stamp.changed.0,
                nanoseconds: stamp.changed.1.try_into().map_err(io::Error::other)?,
            },
            input_remaining_ns: remaining.as_nanos().try_into().map_err(io::Error::other)?,
        };
        transport::check_configuration(&request, self.source.directory()?, file.as_fd(), self.end)?;
        let contents = String::from_utf8(contents)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
        part.request = Some(request);
        part.contents = Some(contents);
        drop(part);
        self.check_current(self.end)
    }
    pub(super) fn check_current(&self, end: Instant) -> io::Result<()> {
        let end = end.min(self.end);
        time(end)?;
        self.source.check_current()?;
        let part = lock(&self.partial, end)?;
        if let Some(root) = &part.root {
            if &Stamp::from(self.source.metadata()?) != root {
                return Err(io::Error::other("configuration source directory changed"));
            }
        }
        for (file, stamp) in &part.parents {
            if &Stamp::from(file.metadata()?) != stamp {
                return Err(io::Error::other("configuration parent changed"));
            }
        }
        if let Some((file, stamp)) = &part.file {
            if &Stamp::from(file.metadata()?) != stamp {
                return Err(io::Error::other("original configuration changed"));
            }
            if let Some(request) = &part.request {
                transport::check_configuration(
                    request,
                    self.source.directory()?,
                    file.as_fd(),
                    end,
                )?;
            }
        }
        self.source.check_current()?;
        time(end)
    }
    pub(super) fn contents(&self, end: Instant) -> io::Result<String> {
        self.check_current(end)?;
        lock(&self.partial, end)?
            .contents
            .clone()
            .ok_or_else(|| io::Error::other("configuration capture is incomplete"))
    }
    pub(super) fn offered(&self, end: Instant) -> io::Result<bool> {
        Ok(lock(&self.partial, end)?.offered)
    }
    pub(super) fn offer(self: &Arc<Self>, end: Instant) -> io::Result<Offer> {
        self.check_current(end)?;
        let part = lock(&self.partial, end)?;
        let request = part
            .request
            .clone()
            .ok_or_else(|| io::Error::other("configuration capture is incomplete"))?;
        let description = part
            .file
            .as_ref()
            .ok_or_else(|| io::Error::other("original configuration is missing"))?
            .0
            .try_clone()?;
        Ok(Offer { original: Arc::clone(self), description, request })
    }
    pub(super) fn mark_offered(&self, end: Instant) -> io::Result<()> {
        self.check_current(end)?;
        lock(&self.partial, end)?.offered = true;
        Ok(())
    }
    #[cfg(test)]
    pub(super) fn retained_descriptions(&self) -> usize {
        let part = self.partial.lock().unwrap();
        part.parents.len() + part.pending.len() + usize::from(part.file.is_some())
    }
}
impl Offer {
    pub(super) fn description(&self, end: Instant) -> io::Result<BorrowedFd<'_>> {
        self.check_current(end)?;
        Ok(self.description.as_fd())
    }
    pub(super) fn check_current(&self, end: Instant) -> io::Result<()> {
        self.original.check_current(end)?;
        transport::check_configuration(
            &self.request,
            self.original.source.directory()?,
            self.description.as_fd(),
            self.original.end.min(end),
        )
    }
}
