//! Warm directories are retained DATA inputs, never old compilation,
//! execution or proof grants. Normal Cargo fingerprints/under-lock checks and
//! the actual new root's output leases remain mandatory on every invocation.
use std::fs::{self, File, OpenOptions};
use std::os::unix::fs::{DirBuilderExt as _, MetadataExt as _, OpenOptionsExt as _};
use std::path::{Path, PathBuf};

use serde_json::{Value, json};
use trust_qualification::{Refusal, Result};

struct Directory {
    path: PathBuf,
    descriptor: File,
    key: (u64, u64),
}
impl Directory {
    fn open(path: &Path) -> Result<Self> {
        match fs::DirBuilder::new().mode(0o700).create(path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error.into()),
        }
        let descriptor = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(path)?;
        let metadata = descriptor.metadata()?;
        let result = Self { path: path.into(), descriptor, key: (metadata.dev(), metadata.ino()) };
        result.check()?;
        Ok(result)
    }
    fn check(&self) -> Result<()> {
        let held = self.descriptor.metadata()?;
        let named = fs::symlink_metadata(&self.path)?;
        if !named.is_dir()
            || named.file_type().is_symlink()
            || (held.dev(), held.ino()) != self.key
            || (named.dev(), named.ino()) != self.key
            || held.uid() != unsafe { libc::geteuid() }
            || named.uid() != held.uid()
            || held.mode() & 0o077 != 0
            || named.mode() & 0o077 != 0
            || !matches!(self.path.canonicalize(),Ok(actual)if actual==self.path)
        {
            return Err(Refusal(
                "original private paired cache directory changed or is aliased/nonprivate".into(),
            ));
        }
        Ok(())
    }
}
pub(super) struct Cache {
    root: Directory,
    sides: [Directory; 2],
}
impl Cache {
    /// Called only after the retained input/output disjointness checks. No
    /// lock is reconstructed here; actual Layout/OFD owners belong to Targo.
    pub fn open(path: &Path) -> Result<Self> {
        if !path.is_absolute()
            || path
                .parent()
                .is_none_or(|parent| !matches!(parent.canonicalize(),Ok(actual)if actual==parent))
        {
            return Err(Refusal(
                "paired cache requires an original normalized existing parent".into(),
            ));
        }
        let root = Directory::open(path)?;
        let sides = [
            Directory::open(&path.join("control-target"))?,
            Directory::open(&path.join("candidate-target"))?,
        ];
        let result = Self { root, sides };
        result.check()?;
        Ok(result)
    }
    pub fn check(&self) -> Result<()> {
        let mut errors = Vec::new();
        for directory in std::iter::once(&self.root).chain(self.sides.iter()) {
            if let Err(error) = directory.check() {
                errors.push(error.0);
            }
        }
        if errors.is_empty() { Ok(()) } else { Err(Refusal(errors.join("; "))) }
    }
    pub fn target(&self, side: trust_qualification::dependencies::Side) -> &Path {
        &self.sides[match side {
            trust_qualification::dependencies::Side::Control => 0,
            trust_qualification::dependencies::Side::Candidate => 1,
        }]
        .path
    }
    pub fn report(&self) -> Value {
        json!({"root":self.root.path,"original_root_device":self.root.key.0,"original_root_inode":self.root.key.1,
            "scope":"retained existing directory/data only; normal current Cargo input/fingerprint/output-lock and kernel-proof checks remain required"})
    }
}

#[cfg(test)]
mod tests {
    use std::os::unix::fs::PermissionsExt as _;

    use super::*;
    #[test]
    fn warm_data_survives_reopening_without_rewriting_fingerprints_or_granting_execution() {
        let temporary = tempfile::tempdir().unwrap();
        let parent = temporary.path().canonicalize().unwrap();
        let path = parent.join("cache");
        let original = Cache::open(&path).unwrap();
        let artifact = original
            .target(trust_qualification::dependencies::Side::Control)
            .join("existing-fingerprint-data");
        fs::write(&artifact, b"existing data, never an execution/proof grant").unwrap();
        let identity = fs::metadata(&artifact).unwrap();
        original.check().unwrap();
        drop(original);
        let next = Cache::open(&path).unwrap();
        next.check().unwrap();
        assert_eq!(fs::read(&artifact).unwrap(), b"existing data, never an execution/proof grant");
        let retained = fs::metadata(&artifact).unwrap();
        assert_eq!((retained.dev(), retained.ino()), (identity.dev(), identity.ino()));
    }
    #[test]
    fn cache_alias_replacement_and_permission_drift_refuse() {
        let temporary = tempfile::tempdir().unwrap();
        let parent = temporary.path().canonicalize().unwrap();
        let path = parent.join("cache");
        let original = Cache::open(&path).unwrap();
        std::os::unix::fs::symlink(&path, parent.join("alias")).unwrap();
        assert!(Cache::open(&parent.join("alias")).is_err());
        fs::rename(&path, parent.join("moved")).unwrap();
        fs::DirBuilder::new().mode(0o700).create(&path).unwrap();
        assert!(original.check().is_err());
        let next = Cache::open(&path).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o777)).unwrap();
        assert!(next.check().is_err());
        assert!(Cache::open(&path).is_err());
    }
}
