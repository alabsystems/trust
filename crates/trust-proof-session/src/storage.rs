//! Bounded untrusted mathematical-hint storage shared by native session owners.
//! No method constructs a certificate, favorable report, CPU grant or source owner.

use std::fs::{self, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub const DIRECTORY: &str = "kernel-proof-artifacts-v2";
pub const MAX_ARTIFACT_BYTES: u64 = 8 * 1024 * 1024;
pub const MAX_SNAPSHOT_BYTES: u64 = 64 * 1024 * 1024;
pub const MAX_SNAPSHOT_FILES: usize = 4096;
// Bound enumeration itself, including unrelated names, before accumulating/sorting hints.
// One full population of overflow permits ordinary pruning without an unbounded scan.
pub const MAX_DIRECTORY_ENTRIES: usize = 2 * MAX_SNAPSHOT_FILES;
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SessionPool {
    schema: u32,
    directory: PathBuf,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ImportBudget {
    schema: u32,
    files: usize,
    bytes: u64,
}

pub fn private_dir(path: &Path) -> io::Result<()> {
    match fs::create_dir(path) {
        Ok(()) => {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                fs::set_permissions(path, fs::Permissions::from_mode(0o700))?;
            }
        }
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(error),
    }
    check_private_dir(path)
}

pub fn check_private_dir(path: &Path) -> io::Result<()> {
    let metadata = fs::symlink_metadata(path)?;
    if !metadata.is_dir() || metadata.file_type().is_symlink() {
        return Err(io::Error::other(
            "proof hint directory is not a real directory",
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if metadata.permissions().mode() & 0o077 != 0 {
            return Err(io::Error::other("proof hint directory is not private"));
        }
    }
    Ok(())
}

pub fn read_bounded(path: &Path) -> io::Result<Vec<u8>> {
    let metadata = fs::symlink_metadata(path)?;
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || metadata.len() > MAX_ARTIFACT_BYTES
    {
        return Err(io::Error::other("invalid proof hint file"));
    }
    #[cfg(unix)]
    let file = fs::File::from(
        nix::fcntl::open(
            path,
            nix::fcntl::OFlag::O_RDONLY
                | nix::fcntl::OFlag::O_NOFOLLOW
                | nix::fcntl::OFlag::O_NONBLOCK,
            nix::sys::stat::Mode::empty(),
        )
        .map_err(io::Error::from)?,
    );
    #[cfg(not(unix))]
    let file = fs::File::open(path)?;
    if !file.metadata()?.is_file() {
        return Err(io::Error::other("proof hint is not a regular file"));
    }
    let mut bytes = Vec::new();
    file.take(MAX_ARTIFACT_BYTES + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_ARTIFACT_BYTES {
        return Err(io::Error::other("oversized proof hint"));
    }
    Ok(bytes)
}

pub fn atomic_write(directory: &Path, name: &str, bytes: &[u8]) -> io::Result<()> {
    atomic_write_with(directory, name, bytes, false)
}

pub fn atomic_write_new(directory: &Path, name: &str, bytes: &[u8]) -> io::Result<()> {
    atomic_write_with(directory, name, bytes, true)
}

fn atomic_write_with(
    directory: &Path,
    name: &str,
    bytes: &[u8],
    exclusive: bool,
) -> io::Result<()> {
    if bytes.len() as u64 > MAX_ARTIFACT_BYTES {
        return Err(io::Error::other("oversized proof hint"));
    }
    private_dir(directory)?;
    let temporary = directory.join(format!(
        ".{}.{}.partial",
        std::process::id(),
        NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
    ));
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options.open(&temporary)?;
    let result = (|| {
        file.write_all(bytes)?;
        file.sync_all()?;
        if exclusive {
            // A complete temporary file becomes visible in one operation.
            // An existing consumed snapshot is never replaced, including when
            // another compiler process imported this key first.
            fs::hard_link(&temporary, directory.join(name))?;
            fs::remove_file(&temporary)
        } else {
            fs::rename(&temporary, directory.join(name))
        }
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result
}

/// Optional per-user mathematical proof hints under STORE-1. There is no cache
/// path override and no stored certificate, verdict, or program authority.
pub struct ProofArtifactStore {
    directory: PathBuf,
}

impl ProofArtifactStore {
    /// Location of untrusted hint bytes, never a proof or execution grant.
    pub fn objects_directory(&self) -> &Path {
        &self.directory
    }

    /// `cargo_home` is Targo's resolved Cargo home. Pure mathematical payloads
    /// are shared across workspaces; current row authority is never stored here.
    pub fn open(cargo_home: &Path) -> io::Result<Self> {
        let directory = cargo_home.join("trust").join("results").join("v1");
        let existing = directory
            .ancestors()
            .find(|path| path.exists())
            .ok_or_else(|| io::Error::other("no existing cache ancestor"))?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if existing.canonicalize()?.ancestors().any(|path| {
                fs::metadata(path).map_or(true, |m| m.permissions().mode() & 0o022 != 0)
            }) {
                return Err(io::Error::other("writable proof cache ancestor"));
            }
        }
        fs::create_dir_all(&directory)?;
        let directory = directory.join(DIRECTORY);
        private_dir(&directory)?;
        let directory = directory.join("objects");
        private_dir(&directory)?;
        let store = Self {
            directory: directory.canonicalize()?,
        };
        store.maintain()?;
        Ok(store)
    }

    /// Prepare exact-key import without reading or copying the proof pool.
    /// The compiler snapshots each demanded object on first use. Concurrent
    /// pool replacement/eviction cannot change bytes already consumed by a run.
    pub fn prepare_session(&self, root: &Path) -> io::Result<()> {
        check_private_dir(root)?;
        let directory = root.join(DIRECTORY);
        private_dir(&directory)?;
        private_dir(&directory.join("incoming"))?;
        // Initialization may share an outgoing-only producer directory, but
        // must never assign a fresh zero budget to already-consumed objects.
        if fs::read_dir(directory.join("incoming"))?.next().is_some() {
            return Err(io::Error::other("proof import snapshot is not empty"));
        }
        let budget = ImportBudget {
            schema: 1,
            files: 0,
            bytes: 0,
        };
        atomic_write_new(
            &directory,
            "import-budget.json",
            &serde_json::to_vec(&budget).map_err(io::Error::other)?,
        )?;
        // Private run configuration, not an imported proof or authority token.
        // The compiler may import a proof published after this session starts.
        let locator = SessionPool {
            schema: 1,
            directory: self.directory.clone(),
        };
        let bytes = serde_json::to_vec(&locator).map_err(io::Error::other)?;
        atomic_write_new(&directory, "pool.json", &bytes)
    }

    pub fn import(&self, root: &Path, name: &str) -> io::Result<Option<PathBuf>> {
        if name.len() != 69
            || !name.ends_with(".json")
            || !name.as_bytes()[..64]
                .iter()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
        {
            return Err(io::Error::other("invalid mathematical hint key"));
        }
        let directory = root.join(DIRECTORY);
        let incoming = directory.join("incoming");
        check_private_dir(&directory)?;
        check_private_dir(&incoming)?;
        let snapshot = incoming.join(name);
        // A malformed consumed snapshot is an ordinary miss, never a reason
        // to replace it from the changing shared pool during this run.
        if fs::symlink_metadata(&snapshot).is_ok() {
            return Ok(Some(snapshot));
        }
        let bytes = match read_bounded(&self.directory.join(name)) {
            Ok(bytes) => bytes,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(error),
        };
        let Some(lease) = trust_file_lock::try_exclusive_work_lock(&directory.join("import"))
            .map_err(io::Error::other)?
        else {
            return Ok(None);
        };
        if fs::symlink_metadata(&snapshot).is_ok() {
            return Ok(Some(snapshot));
        }
        let mut budget: ImportBudget =
            serde_json::from_slice(&read_bounded(&directory.join("import-budget.json"))?)
                .map_err(io::Error::other)?;
        if budget.schema != 1
            || budget.files > MAX_SNAPSHOT_FILES
            || budget.bytes > MAX_SNAPSHOT_BYTES
        {
            return Err(io::Error::other("invalid proof import budget"));
        }
        let count = budget
            .files
            .checked_add(1)
            .filter(|count| *count <= MAX_SNAPSHOT_FILES);
        let size = budget
            .bytes
            .checked_add(bytes.len() as u64)
            .filter(|size| *size <= MAX_SNAPSHOT_BYTES);
        let (Some(count), Some(size)) = (count, size) else {
            return Ok(None);
        };
        budget.files = count;
        budget.bytes = size;
        lease.validate().map_err(io::Error::other)?;
        // Reserve first: a crash can waste this session's optional hint budget,
        // but can never publish unaccounted bytes or reset consumed capacity.
        atomic_write(
            &directory,
            "import-budget.json",
            &serde_json::to_vec(&budget).map_err(io::Error::other)?,
        )?;
        lease.validate().map_err(io::Error::other)?;
        atomic_write_new(&incoming, name, &bytes)?;
        Ok(Some(snapshot))
    }

    pub fn from_session(root: &Path) -> Option<Self> {
        check_private_dir(root).ok()?;
        check_private_dir(&root.join(DIRECTORY)).ok()?;
        let locator: SessionPool =
            serde_json::from_slice(&read_bounded(&root.join(DIRECTORY).join("pool.json")).ok()?)
                .ok()?;
        let suffix = Path::new("trust")
            .join("results")
            .join("v1")
            .join(DIRECTORY)
            .join("objects");
        if locator.schema != 1
            || !locator.directory.is_absolute()
            || !locator.directory.ends_with(suffix)
            || locator.directory.canonicalize().ok()? != locator.directory
            || check_private_dir(&locator.directory).is_err()
        {
            return None;
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if locator.directory.ancestors().any(|path| {
                fs::symlink_metadata(path).map_or(true, |m| {
                    !m.is_dir() || m.file_type().is_symlink() || m.permissions().mode() & 0o022 != 0
                })
            }) {
                return None;
            }
        }
        Some(Self {
            directory: locator.directory,
        })
    }

    pub fn try_search_lease(
        &self,
        violation: &[u8],
    ) -> io::Result<Option<trust_file_lock::ExclusiveWorkLock>> {
        let parent = self
            .directory
            .parent()
            .ok_or_else(|| io::Error::other("no pool parent"))?;
        let locks = parent.join("search-locks");
        private_dir(&locks)?;
        // Stable bounded stripes are never removed by proof retention. A hash
        // collision can delay another search, never supply a different proof.
        let stripe = Sha256::digest(violation)[0];
        let resource = locks.join(format!("proof-{stripe:02x}"));
        trust_file_lock::try_exclusive_work_lock(&resource).map_err(io::Error::other)
    }

    /// Called only after Targo's successful run. Even these bytes remain hints
    /// and have to earn new current-process authority on every import.
    pub fn publish_session(&self, root: &Path) -> io::Result<usize> {
        let outgoing = root.join(DIRECTORY).join("outgoing");
        let count = if outgoing.exists() {
            self.copy_to(&outgoing, &self.directory)?
        } else {
            0
        };
        self.maintain()?;
        Ok(count)
    }

    /// Retain completed mathematical hints within the pool budget, including
    /// after a caller failed elsewhere. This never publishes a program verdict.
    pub fn maintain(&self) -> io::Result<()> {
        self.prune_to_budget(MAX_SNAPSHOT_FILES, MAX_SNAPSHOT_BYTES)
    }

    pub fn copy_to(&self, from: &Path, to: &Path) -> io::Result<usize> {
        check_private_dir(from)?;
        if let Some(parent) = to.parent() {
            private_dir(parent)?;
        }
        private_dir(to)?;
        let mut count = 0;
        let mut total = 0;
        for file in proof_files(from)? {
            if count == MAX_SNAPSHOT_FILES {
                break;
            }
            if file.bytes > MAX_ARTIFACT_BYTES || total + file.bytes > MAX_SNAPSHOT_BYTES {
                continue;
            }
            let Ok(bytes) = read_bounded(&from.join(&file.name)) else {
                continue;
            };
            if total + bytes.len() as u64 > MAX_SNAPSHOT_BYTES {
                continue;
            }
            atomic_write(to, &file.name, &bytes)?;
            count += 1;
            total += bytes.len() as u64;
        }
        Ok(count)
    }

    // Only completed files owned by this component are candidates. Recency
    // chooses hints to retain; it is never consulted for proof validity.
    // Concurrent publishers may evict a just-replaced hint. A reader already
    // holds its private copy, or takes an ordinary miss and reconstructs.
    pub fn prune_to_budget(&self, max_files: usize, max_bytes: u64) -> io::Result<()> {
        if max_files > MAX_SNAPSHOT_FILES || max_bytes > MAX_SNAPSHOT_BYTES {
            return Err(io::Error::other(
                "proof hint maintenance cannot enlarge the storage budget",
            ));
        }
        check_private_dir(&self.directory)?;
        let mut count = 0;
        let mut bytes = 0;
        for file in proof_files(&self.directory)? {
            if file.bytes <= MAX_ARTIFACT_BYTES
                && count < max_files
                && bytes + file.bytes <= max_bytes
            {
                count += 1;
                bytes += file.bytes;
            } else if let Err(error) = fs::remove_file(self.directory.join(&file.name)) {
                if error.kind() != io::ErrorKind::NotFound {
                    return Err(error);
                }
            }
        }
        Ok(())
    }
}

pub struct ProofFile {
    pub name: String,
    pub bytes: u64,
    pub modified: std::time::SystemTime,
}

pub fn proof_files(directory: &Path) -> io::Result<Vec<ProofFile>> {
    let mut files = Vec::new();
    for (index, entry) in fs::read_dir(directory)?.enumerate() {
        if index == MAX_DIRECTORY_ENTRIES {
            return Err(io::Error::other(
                "proof hint directory population exceeds bounded scan",
            ));
        }
        let entry = entry?;
        let Ok(name) = entry.file_name().into_string() else {
            continue;
        };
        let Some(key) = name.strip_suffix(".json") else {
            continue;
        };
        if key.len() != 64 || !key.bytes().all(|c| c.is_ascii_hexdigit()) {
            continue;
        }
        let Ok(metadata) = fs::symlink_metadata(entry.path()) else {
            continue;
        };
        if !metadata.is_file() || metadata.file_type().is_symlink() {
            continue;
        }
        files.push(ProofFile {
            name,
            bytes: metadata.len(),
            modified: metadata
                .modified()
                .unwrap_or(std::time::SystemTime::UNIX_EPOCH),
        });
    }
    files.sort_by(|a, b| {
        b.modified
            .cmp(&a.modified)
            .then_with(|| a.name.cmp(&b.name))
    });
    Ok(files)
}
