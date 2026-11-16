//! Bounded reads of actual files, with same-handle drift checks.

use std::fs::{self, File, Metadata, OpenOptions};
use std::io::Read as _;
use std::path::{Path, PathBuf};

use trust_sha2::{Digest as _, Sha256};

use crate::{Refusal, Result};

#[cfg(unix)]
pub(crate) fn stamp(metadata: &Metadata) -> (u64, u64, u32, u64, i64, i64, i64, i64) {
    use std::os::unix::fs::MetadataExt as _;
    (
        metadata.dev(),
        metadata.ino(),
        metadata.mode(),
        metadata.len(),
        metadata.mtime(),
        metadata.mtime_nsec(),
        metadata.ctime(),
        metadata.ctime_nsec(),
    )
}

pub(crate) struct Loaded {
    pub(crate) bytes: Vec<u8>,
    path: PathBuf,
    file: File,
    metadata: Metadata,
}

impl Loaded {
    pub(crate) fn check_current(&self) -> Result<()> {
        #[cfg(unix)]
        if stamp(&self.metadata) != stamp(&self.file.metadata()?)
            || stamp(&self.metadata) != stamp(&fs::symlink_metadata(&self.path)?)
        {
            return Err(Refusal("receipt changed while checking its stage files".into()));
        }
        Ok(())
    }
}

pub(crate) fn read_receipt(path: &Path, limit: u64) -> Result<Option<Loaded>> {
    let before = match fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(Refusal(format!("it cannot be inspected: {error}"))),
    };
    if !before.is_file() {
        return Err(Refusal(
            "it is not a regular file; a seal cannot carry a receipt it only points at".into(),
        ));
    }
    if before.len() > limit {
        return Err(Refusal(format!("it is {} bytes, more than {limit}", before.len())));
    }
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC);
    }
    let mut file =
        options.open(path).map_err(|error| Refusal(format!("it cannot be read: {error}")))?;
    #[cfg(unix)]
    if stamp(&before) != stamp(&file.metadata()?) {
        return Err(Refusal("receipt changed before it could be read".into()));
    }
    let mut bytes = Vec::new();
    file.by_ref().take(limit + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > limit || bytes.len() as u64 != before.len() {
        return Err(Refusal("receipt changed or exceeded its byte bound while reading".into()));
    }
    let loaded = Loaded { bytes, path: path.into(), file, metadata: before };
    loaded.check_current()?;
    Ok(Some(loaded))
}

/// Compatibility aliases may be links. Compare their actual target bytes, as
/// the legacy reader does, without turning that into complete seal coverage.
pub(crate) fn hash_file(path: &Path) -> Result<String> {
    let before = fs::metadata(path)?;
    if !before.is_file() {
        return Err(Refusal(format!("{} is not a regular file", path.display())));
    }
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NONBLOCK | libc::O_CLOEXEC);
    }
    let mut file = options.open(path)?;
    let opened = file.metadata()?;
    if !opened.is_file() {
        return Err(Refusal("recorded stage file changed kind before opening".into()));
    }
    #[cfg(unix)]
    if stamp(&before) != stamp(&opened) {
        return Err(Refusal("recorded stage file changed before opening".into()));
    }
    let mut hash = Sha256::new();
    let mut total = 0u64;
    let mut buffer = vec![0; 1024 * 1024];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        total = total
            .checked_add(read as u64)
            .ok_or_else(|| Refusal("stage file size overflow".into()))?;
        if total > opened.len() {
            return Err(Refusal("recorded stage file grew while hashing".into()));
        }
        hash.update(&buffer[..read]);
    }
    if total != opened.len() {
        return Err(Refusal("recorded stage file shortened while hashing".into()));
    }
    #[cfg(unix)]
    if stamp(&opened) != stamp(&file.metadata()?) || stamp(&opened) != stamp(&fs::metadata(path)?) {
        return Err(Refusal("recorded stage file changed while hashing".into()));
    }
    Ok(format!("{:x}", hash.finalize()))
}
