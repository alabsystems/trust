use std::env;
use std::ffi::OsStr;
use std::fs;
use std::io;
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static SCRATCH_COUNTER: AtomicU64 = AtomicU64::new(0);

pub struct ScratchDir {
    path: PathBuf,
}

impl ScratchDir {
    pub fn new(label: &str) -> io::Result<Self> {
        let root = env::temp_dir().join("trust-hardened-walkthroughs");
        fs::create_dir_all(&root)?;

        let label = safe_label(label);
        let pid = std::process::id();
        let nanos = SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_nanos();

        for _ in 0..128 {
            let counter = SCRATCH_COUNTER.fetch_add(1, Ordering::Relaxed);
            let candidate = root.join(format!("{label}-{pid}-{nanos}-{counter}"));
            match fs::create_dir(&candidate) {
                Ok(()) => return Ok(Self { path: candidate }),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error),
            }
        }

        Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            "could not create unique hardened walkthrough scratch directory",
        ))
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn path_for(&self, leaf: &OsStr) -> io::Result<PathBuf> {
        let relative = Path::new(leaf);
        let mut components = relative.components();
        match (components.next(), components.next()) {
            (Some(Component::Normal(_)), None) => Ok(self.path.join(relative)),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "scratch paths must be single relative path components",
            )),
        }
    }

    pub fn write_file(&self, leaf: &OsStr, contents: &[u8]) -> io::Result<PathBuf> {
        let path = self.path_for(leaf)?;
        fs::write(&path, contents)?;
        Ok(path)
    }
}

impl Drop for ScratchDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[cfg(unix)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnixFileId {
    pub dev: u64,
    pub ino: u64,
}

#[cfg(unix)]
impl std::fmt::Display for UnixFileId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{}:{}", self.dev, self.ino)
    }
}

#[cfg(unix)]
pub fn unix_file_id(path: &Path) -> io::Result<UnixFileId> {
    use std::os::unix::fs::MetadataExt;

    let metadata = fs::metadata(path)?;
    Ok(UnixFileId { dev: metadata.dev(), ino: metadata.ino() })
}

pub fn hex_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 0x0f) as usize] as char);
    }
    encoded
}

fn safe_label(label: &str) -> String {
    let mut sanitized = String::with_capacity(label.len().max(1));
    for byte in label.bytes() {
        match byte {
            b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'-' | b'_' => {
                sanitized.push(byte as char);
            }
            _ => sanitized.push('_'),
        }
    }

    if sanitized.is_empty() {
        sanitized.push_str("scratch");
    }

    sanitized
}
