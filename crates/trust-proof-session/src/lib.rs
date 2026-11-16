//! One fresh verification run and its untrusted mathematical hints.
//!
//! This owner supplies freshness and private input lifetime. It supplies no
//! compiler/source authority, CPU credit, favorable verdict or certificate.
//! Native callers must independently retain their original admission, command,
//! source, SDK and output owners through actual child retirement.

use std::fs::{self, File};
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};

pub mod storage;
pub use storage::ProofArtifactStore;

/// Neither a saved nonce nor a decoded report can construct this owner.
/// Every constructor creates a new private directory and obtains fresh native
/// randomness. There is deliberately no Clone, Deserialize or restore API.
pub struct VerificationSession {
    directory: Option<tempfile::TempDir>,
    artifact_root: PathBuf,
    id: String,
    proof_store: Option<ProofArtifactStore>,
    poisoned: AtomicBool,
    #[cfg(unix)]
    original: File,
    #[cfg(unix)]
    relative_parent: Option<(File, std::ffi::OsString)>,
}

impl VerificationSession {
    pub fn create() -> io::Result<Self> {
        Self::from_fresh_directory(
            tempfile::Builder::new()
                .prefix("trust-proof-artifact-root-")
                .tempdir()?,
        )
    }

    /// Create within a caller's original output directory. A path is only a
    /// location: the caller must still hold and check its actual output lease.
    pub fn create_in(parent: &Path) -> io::Result<Self> {
        let metadata = fs::symlink_metadata(parent)?;
        if !parent.is_absolute()
            || parent.components().any(|part| {
                matches!(
                    part,
                    std::path::Component::ParentDir | std::path::Component::CurDir
                )
            })
            || metadata.file_type().is_symlink()
            || !metadata.is_dir()
            || parent.canonicalize()? != parent
        {
            return Err(io::Error::other(
                "verification session output is not an original normalized directory",
            ));
        }
        Self::from_fresh_directory(
            tempfile::Builder::new()
                .prefix("trust-proof-artifact-root-")
                .tempdir_in(parent)?,
        )
    }

    /// Native preparation through the caller's SAME actual parent directory.
    /// The pathname is checked location DATA. It neither opens/reconstructs
    /// that original nor supplies output exclusion, CPU or FD admission.
    /// Callers must reserve real descriptor capacity before this method.
    #[cfg(unix)]
    pub fn create_at(parent: std::os::fd::BorrowedFd<'_>, location: &Path) -> io::Result<Self> {
        use std::os::fd::AsFd as _;
        let parent = File::from(parent.try_clone_to_owned()?);
        check_parent(&parent, location)?;
        let mut nonce = [0u8; 32];
        getrandom::fill(&mut nonce).map_err(|error| {
            io::Error::other(format!("verification randomness unavailable: {error}"))
        })?;
        let mut namespace = [0u8; 16];
        getrandom::fill(&mut namespace).map_err(|error| {
            io::Error::other(format!(
                "verification namespace randomness unavailable: {error}"
            ))
        })?;
        let suffix: String = namespace.iter().map(|byte| format!("{byte:02x}")).collect();
        let leaf = std::ffi::OsString::from(format!("trust-proof-artifact-root-{suffix}"));
        nix::sys::stat::mkdirat(
            parent.as_fd(),
            leaf.as_os_str(),
            nix::sys::stat::Mode::S_IRWXU,
        )
        .map_err(io::Error::from)?;
        let original = File::from(
            nix::fcntl::openat(
                parent.as_fd(),
                leaf.as_os_str(),
                nix::fcntl::OFlag::O_RDONLY
                    | nix::fcntl::OFlag::O_DIRECTORY
                    | nix::fcntl::OFlag::O_NOFOLLOW
                    | nix::fcntl::OFlag::O_CLOEXEC,
                nix::sys::stat::Mode::empty(),
            )
            .map_err(io::Error::from)?,
        );
        let result = Self {
            directory: None,
            artifact_root: location.join(&leaf),
            id: nonce.iter().map(|byte| format!("{byte:02x}")).collect(),
            proof_store: None,
            poisoned: AtomicBool::new(false),
            original,
            relative_parent: Some((parent, leaf)),
        };
        result.check_current()?;
        Ok(result)
    }

    /// A new fixed metadata namespace below the actual session description.
    /// Existing entries refuse. This supplies no compiler/write authority.
    #[cfg(unix)]
    pub fn prepare_metadata(&self) -> io::Result<MetadataDirectory> {
        use std::os::fd::AsFd as _;
        self.check_current()?;
        nix::sys::stat::mkdirat(
            self.original.as_fd(),
            "metadata",
            nix::sys::stat::Mode::S_IRWXU,
        )
        .map_err(io::Error::from)?;
        let file = File::from(
            nix::fcntl::openat(
                self.original.as_fd(),
                "metadata",
                nix::fcntl::OFlag::O_RDONLY
                    | nix::fcntl::OFlag::O_DIRECTORY
                    | nix::fcntl::OFlag::O_NOFOLLOW
                    | nix::fcntl::OFlag::O_CLOEXEC,
                nix::sys::stat::Mode::empty(),
            )
            .map_err(io::Error::from)?,
        );
        let result = MetadataDirectory {
            file,
            path: self.artifact_root.join("metadata"),
            poisoned: AtomicBool::new(false),
        };
        self.check_current()?;
        result.check_current()?;
        Ok(result)
    }

    fn from_fresh_directory(directory: tempfile::TempDir) -> io::Result<Self> {
        let mut nonce = [0u8; 32];
        getrandom::fill(&mut nonce).map_err(|error| {
            io::Error::other(format!(
                "operating-system randomness failed while creating verification session: {error}"
            ))
        })?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            fs::set_permissions(directory.path(), fs::Permissions::from_mode(0o700))?;
        }
        let artifact_root = directory.path().canonicalize()?;
        #[cfg(unix)]
        let original = {
            use std::os::unix::fs::OpenOptionsExt as _;
            fs::OpenOptions::new()
                .read(true)
                .custom_flags(nix::libc::O_DIRECTORY | nix::libc::O_NOFOLLOW | nix::libc::O_CLOEXEC)
                .open(&artifact_root)?
        };
        let session = Self {
            directory: Some(directory),
            artifact_root,
            id: nonce.iter().map(|byte| format!("{byte:02x}")).collect(),
            proof_store: None,
            poisoned: AtomicBool::new(false),
            #[cfg(unix)]
            original,
            #[cfg(unix)]
            relative_parent: None,
        };
        session.check_current()?;
        Ok(session)
    }

    pub fn id(&self) -> &str {
        &self.id
    }

    /// A borrowed location, not authority to dispatch or a proof result.
    pub fn artifact_root(&self) -> &Path {
        &self.artifact_root
    }

    /// Optional hints keep the existing ordinary-search fallback semantics.
    /// The caller supplies its already resolved Cargo home, never an override
    /// for a proof pool or an authority reconstructed from stored data.
    #[must_use]
    pub fn with_proof_store(mut self, cargo_home: Option<&Path>) -> Self {
        self.proof_store = cargo_home.and_then(|home| {
            self.check_current().ok()?;
            let store = ProofArtifactStore::open(home).ok()?;
            store.prepare_session(self.artifact_root()).ok()?;
            Some(store)
        });
        self
    }

    /// Check the same actual private directory. An observed substitution or
    /// privacy failure permanently vetoes this session, including after ABA.
    pub fn check_current(&self) -> io::Result<()> {
        if self.poisoned.load(Ordering::Acquire) {
            return Err(io::Error::other(
                "verification session previously lost its original private directory",
            ));
        }
        let checked = (|| {
            #[cfg(unix)]
            if let Some((parent, leaf)) = &self.relative_parent {
                use std::os::fd::AsFd as _;
                use std::os::unix::fs::MetadataExt as _;
                check_parent(
                    parent,
                    self.artifact_root
                        .parent()
                        .ok_or_else(|| io::Error::other("session parent absent"))?,
                )?;
                let named = File::from(
                    nix::fcntl::openat(
                        parent.as_fd(),
                        leaf.as_os_str(),
                        nix::fcntl::OFlag::O_RDONLY
                            | nix::fcntl::OFlag::O_DIRECTORY
                            | nix::fcntl::OFlag::O_NOFOLLOW
                            | nix::fcntl::OFlag::O_CLOEXEC,
                        nix::sys::stat::Mode::empty(),
                    )
                    .map_err(io::Error::from)?,
                );
                let actual = named.metadata()?;
                let held = self.original.metadata()?;
                if (actual.dev(), actual.ino()) != (held.dev(), held.ino()) {
                    return Err(io::Error::other("session relative original was replaced"));
                }
            }
            storage::check_private_dir(&self.artifact_root)?;
            let named = fs::symlink_metadata(&self.artifact_root)?;
            if self.artifact_root.canonicalize()? != self.artifact_root {
                return Err(io::Error::other(
                    "verification session directory was replaced",
                ));
            }
            #[cfg(unix)]
            {
                use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};
                let held = self.original.metadata()?;
                if !held.is_dir()
                    || (held.dev(), held.ino()) != (named.dev(), named.ino())
                    || held.uid() != named.uid()
                    || held.permissions().mode() & 0o777 != 0o700
                    || named.permissions().mode() & 0o777 != 0o700
                {
                    return Err(io::Error::other(
                        "verification session lost its original private directory",
                    ));
                }
            }
            #[cfg(not(unix))]
            let _ = named;
            Ok(())
        })();
        if checked.is_err() {
            self.poisoned.store(true, Ordering::Release);
        }
        checked
    }

    /// Publish only mathematical bytes. A caller's separate current report
    /// gate decides whether to call this; no result or grade is stored here.
    pub fn publish_proof_hints(&self) {
        if self.check_current().is_ok() {
            if let Some(store) = &self.proof_store {
                let _ = store.publish_session(self.artifact_root());
            }
        }
    }
}

impl Drop for VerificationSession {
    fn drop(&mut self) {
        if self.directory.is_some() {
            if let Some(store) = &self.proof_store {
                // Preserve ordinary frontend maintenance on either exit path.
                let _ = store.maintain();
            }
            if self.check_current().is_err() {
                // TempDir's pathname cleanup must never delete a replacement.
                // Unknown keeps the original/private namespace for diagnosis.
                if let Some(directory) = self.directory.take() {
                    let _ = directory.keep();
                }
            }
        }
        // Native relative sessions deliberately retain their namespace under
        // the original output. Explicit guarded output maintenance, after
        // actual graph retirement, owns later deletion; this Drop grants none.
        // Their caller explicitly publishes/maintains hints while it still
        // owns actual preparation. Deferred Drop must not start that I/O after
        // the caller returned its native CPU reservation or parked the graph.
    }
}

#[cfg(unix)]
fn check_parent(parent: &File, path: &Path) -> io::Result<()> {
    use std::os::unix::fs::MetadataExt as _;
    let held = parent.metadata()?;
    let named = fs::symlink_metadata(path)?;
    if !path.is_absolute()
        || path.canonicalize()? != path
        || !held.is_dir()
        || !named.is_dir()
        || named.file_type().is_symlink()
        || (held.dev(), held.ino()) != (named.dev(), named.ino())
    {
        return Err(io::Error::other(
            "session parent location does not name the actual original description",
        ));
    }
    Ok(())
}

/// Actual mutable compiler metadata directory; no source, proof or write grant.
#[cfg(unix)]
pub struct MetadataDirectory {
    file: File,
    path: PathBuf,
    poisoned: AtomicBool,
}
#[cfg(unix)]
impl MetadataDirectory {
    pub fn path(&self) -> &Path {
        &self.path
    }
    pub fn check_current(&self) -> io::Result<()> {
        use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};
        if self.poisoned.load(Ordering::Acquire) {
            return Err(io::Error::other("metadata original previously failed"));
        }
        let result = (|| {
            let held = self.file.metadata()?;
            let named = fs::symlink_metadata(&self.path)?;
            if !held.is_dir()
                || !named.is_dir()
                || named.file_type().is_symlink()
                || self.path.canonicalize()? != self.path
                || (held.dev(), held.ino()) != (named.dev(), named.ino())
                || held.permissions().mode() & 0o777 != 0o700
                || named.permissions().mode() & 0o777 != 0o700
            {
                return Err(io::Error::other(
                    "metadata original was replaced or lost privacy",
                ));
            }
            Ok(())
        })();
        if result.is_err() {
            self.poisoned.store(true, Ordering::Release);
        }
        result
    }
}

#[cfg(test)]
mod tests;
