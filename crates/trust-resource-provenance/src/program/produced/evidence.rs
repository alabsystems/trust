// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Bounded raw failure evidence beneath the live original output root. This
//! explicit writer creates new files only. SDK/source discovery stays read-only;
//! no observation here establishes successful execution or positive retirement.

use std::io::Write as _;
use std::sync::Mutex;

use super::*;

const DIRECTORY: &str = ".trust-workload-evidence.noindex";
const MAX_BYTES: u64 = 1024 * 1024 * 1024;
const MAX_FILES: u32 = 4096;

struct Budget {
    remaining: u64,
    files: u32,
}
struct Backing {
    output: Arc<OutputBacking>,
    path: PathBuf,
    directory: File,
    before: Metadata,
    budget: Mutex<Budget>,
}
impl Backing {
    fn validate(&self, deadline: Instant) -> io::Result<()> {
        self.output.validate(deadline)?;
        let current = directory(&self.path, deadline)?;
        for file in [&self.directory, &current] {
            if !same_directory(&self.before, &owned(file, true, false)?, false) {
                return Err(refused("original workload evidence directory changed"));
            }
        }
        Ok(())
    }
}

/// Original directory and shared aggregate byte/file bound. This writer has no
/// API for opening old evidence, unlinking files or exposing an unbounded FD.
pub struct HeldEvidenceRoot {
    backing: Arc<Backing>,
}
impl HeldEvidenceRoot {
    pub fn path(&self) -> &Path {
        &self.backing.path
    }
    pub fn create(
        &mut self,
        name: &OsStr,
        byte_limit: u64,
        deadline: Instant,
    ) -> io::Result<BoundedEvidenceFile> {
        self.backing.validate(deadline)?;
        let bytes = name.as_bytes();
        if bytes.is_empty()
            || bytes.len() > 255
            || bytes.contains(&0)
            || bytes.contains(&b'/')
            || matches!(bytes, b"." | b"..")
            || byte_limit == 0
            || byte_limit > MAX_BYTES
        {
            return Err(refused("workload evidence filename or byte bound is invalid"));
        }
        let mut budget = self
            .backing
            .budget
            .lock()
            .map_err(|_| refused("workload evidence budget unavailable"))?;
        if budget.files == 0 {
            return Err(refused("workload evidence file bound exhausted"));
        }
        // Failed or uncertain creation never restores a reusable allocation.
        budget.files -= 1;
        let leaf = name.to_os_string();
        let name =
            CString::new(bytes).map_err(|_| refused("workload evidence filename contains NUL"))?;
        // SAFETY: the original directory is held, the name is one bounded leaf,
        // and exclusive creation neither follows nor overwrites an old entry.
        let fd = unsafe {
            libc::openat(
                self.backing.directory.as_raw_fd(),
                name.as_ptr(),
                libc::O_WRONLY
                    | libc::O_CREAT
                    | libc::O_EXCL
                    | libc::O_NOFOLLOW
                    | libc::O_CLOEXEC
                    | libc::O_NONBLOCK,
                0o600,
            )
        };
        if fd < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: successful exclusive open transferred this fresh description.
        let file = unsafe { File::from_raw_fd(fd) };
        let before = owned(&file, false, false)?;
        if before.nlink() != 1 || before.len() != 0 {
            return Err(refused("new workload evidence file is aliased or nonempty"));
        }
        drop(budget);
        self.backing.validate(deadline)?;
        Ok(BoundedEvidenceFile {
            backing: Arc::clone(&self.backing),
            file,
            name: leaf,
            identity: identity(&before),
            limit: byte_limit,
            written: 0,
        })
    }
}

/// A raw prefix writer. Quota/IO failures leave the actual written prefix and
/// must be reported as incomplete. Call sync_prefix before an owning-custody
/// Unknown abort; a successful sync still grants no completion or retirement.
pub struct BoundedEvidenceFile {
    backing: Arc<Backing>,
    file: File,
    name: OsString,
    identity: FileId,
    limit: u64,
    written: u64,
}
impl BoundedEvidenceFile {
    pub fn bytes_written(&self) -> u64 {
        self.written
    }
    fn validate(&self, deadline: Instant) -> io::Result<()> {
        self.backing.validate(deadline)?;
        let meta = owned(&self.file, false, false)?;
        let current = openat(self.backing.directory.as_raw_fd(), &self.name, false)?;
        let named = owned(&current, false, false)?;
        if identity(&meta) != self.identity || meta.nlink() != 1 || meta.len() != self.written {
            return Err(refused("original workload evidence backing changed"));
        }
        if identity(&named) != self.identity || named.nlink() != 1 || named.len() != self.written {
            return Err(refused("original workload evidence name was replaced"));
        }
        Ok(())
    }
    pub fn append(&mut self, bytes: &[u8], deadline: Instant) -> io::Result<usize> {
        self.validate(deadline)?;
        if bytes.is_empty() {
            return Ok(0);
        }
        let mut budget = self
            .backing
            .budget
            .lock()
            .map_err(|_| refused("workload evidence budget unavailable"))?;
        let count =
            (bytes.len() as u64).min(self.limit - self.written).min(budget.remaining) as usize;
        if count == 0 {
            return Err(io::Error::new(
                io::ErrorKind::StorageFull,
                "workload evidence byte bound exhausted",
            ));
        }
        // Reserve before IO. Unknown/partial writes never manufacture another
        // budget. Only the actual returned byte count becomes prefix evidence.
        budget.remaining -= count as u64;
        let written = self.file.write(&bytes[..count])?;
        self.written += written as u64;
        Ok(written)
    }
    pub fn sync_prefix(&self, deadline: Instant) -> io::Result<()> {
        self.validate(deadline)?;
        self.file.sync_all()?;
        self.backing.directory.sync_all()?;
        self.validate(deadline)
    }
}

fn create_directory(parent: &File, name: &OsStr, new: bool) -> io::Result<File> {
    let name_c =
        CString::new(name.as_bytes()).map_err(|_| refused("invalid evidence directory leaf"))?;
    // SAFETY: held original parent, one literal/encoded bounded leaf, no replace.
    let result = unsafe { libc::mkdirat(parent.as_raw_fd(), name_c.as_ptr(), 0o700) };
    if result != 0 {
        let error = io::Error::last_os_error();
        if new || error.kind() != io::ErrorKind::AlreadyExists {
            return Err(error);
        }
    }
    let file = openat(parent.as_raw_fd(), name, true)?;
    owned(&file, true, false)?;
    Ok(file)
}

pub(super) fn prepare(
    output: Arc<OutputBacking>,
    attempt: [u8; 16],
    total: u64,
    files: u32,
    deadline: Instant,
) -> io::Result<HeldEvidenceRoot> {
    if attempt == [0; 16] || total == 0 || total > MAX_BYTES || files == 0 || files > MAX_FILES {
        return Err(refused("workload evidence attempt or aggregate bounds are invalid"));
    }
    output.validate(deadline)?;
    let parent = create_directory(&output.file, OsStr::new(DIRECTORY), false)?;
    let leaf = crate::schema::hex(&attempt);
    let directory = create_directory(&parent, OsStr::new(&leaf), true)?;
    let before = owned(&directory, true, false)?;
    directory.sync_all()?;
    parent.sync_all()?;
    output.file.sync_all()?;
    let path = output.path.join(DIRECTORY).join(leaf);
    let backing = Arc::new(Backing {
        output,
        path,
        directory,
        before,
        budget: Mutex::new(Budget { remaining: total, files }),
    });
    backing.validate(deadline)?;
    Ok(HeldEvidenceRoot { backing })
}
