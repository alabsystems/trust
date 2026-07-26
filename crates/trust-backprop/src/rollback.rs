//! Rollback capabilities for source rewrites.
//!
//! Creates checkpoints of file state before rewrites and supports reverting
//! to the checkpoint if rewrites cause problems (e.g., test failures).
//! Uses SHA-256 hashes to verify rollback integrity.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use trust_types::fx::FxHashMap;

use serde::{Deserialize, Serialize};
use trust_types::stable_sha256_hex;
use thiserror::Error;

/// Errors from checkpoint and rollback operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum RollbackError {
    /// An I/O error reading or writing a file during checkpoint/rollback.
    #[error("I/O error on `{path}`: {source}")]
    Io { path: String, source: std::io::Error },
    /// The file hash after rollback does not match the checkpoint.
    #[error("rollback verification failed for `{path}`: expected hash {expected}, got {actual}")]
    VerificationFailed { path: String, expected: String, actual: String },
    /// The checkpoint file could not be deserialized.
    #[error("checkpoint deserialization failed: {0}")]
    Deserialize(String),
    /// The checkpoint file could not be serialized.
    #[error("checkpoint serialization failed: {0}")]
    Serialize(String),
    /// A checkpoint's stored content does not match its integrity digest.
    #[error("checkpoint snapshot hash mismatch for `{path}`: expected {expected}, got {actual}")]
    InvalidSnapshotHash { path: String, expected: String, actual: String },
    /// A checkpoint contains the same canonical file more than once.
    #[error("checkpoint contains duplicate path `{path}`")]
    DuplicatePath { path: String },
    /// Conditional rollback refused to overwrite a later external edit.
    #[error(
        "rollback refused concurrent modification of `{path}`: expected {expected}, got {actual}"
    )]
    ConcurrentModification { path: String, expected: String, actual: String },
    /// A checkpoint-store identifier could escape or alias the store namespace.
    #[error("invalid checkpoint id `{id}`")]
    InvalidCheckpointId { id: String },
    /// A checkpoint-store entry is not a regular, non-symlink file.
    #[error("unsafe checkpoint-store entry `{path}`")]
    UnsafeStoreEntry { path: String },
    /// Stored content claimed an identity different from the requested file.
    #[error("checkpoint identity mismatch: requested `{requested}`, stored `{stored}`")]
    IdentityMismatch { requested: String, stored: String },
}

/// Snapshot of a single file's state at checkpoint time.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileSnapshot {
    /// The file path (absolute or relative to project root).
    pub path: PathBuf,
    /// The file contents at checkpoint time.
    pub contents: String,
    /// SHA-256 hash of the contents for integrity verification.
    pub hash: String,
}

/// A checkpoint capturing the state of one or more files before rewriting.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RewriteCheckpoint {
    /// Unique identifier for this checkpoint.
    pub id: String,
    /// When the checkpoint was created (ISO 8601 timestamp or epoch seconds).
    pub created_at: String,
    /// Snapshots of each file at checkpoint time.
    pub snapshots: Vec<FileSnapshot>,
}

impl RewriteCheckpoint {
    /// Number of files in this checkpoint.
    #[must_use]
    pub fn file_count(&self) -> usize {
        self.snapshots.len()
    }

    /// Whether this checkpoint is empty (no files).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.snapshots.is_empty()
    }

    /// Get the snapshot for a specific file path, if it exists.
    #[must_use]
    pub fn get_snapshot(&self, path: &Path) -> Option<&FileSnapshot> {
        // `create_checkpoint` stores canonical paths to collapse aliases and
        // reject duplicate targets. Apply the same identity rule to lookups so
        // callers may use the spelling they originally supplied (notably
        // `/var/...` on platforms where it resolves through `/private/var`).
        let canonical = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
        self.snapshots.iter().find(|snapshot| snapshot.path == canonical)
    }
}

/// Persistent store for checkpoints, backed by a directory on disk.
#[derive(Debug, Clone)]
pub struct CheckpointStore {
    /// Directory where checkpoint files are stored.
    store_dir: PathBuf,
}

impl CheckpointStore {
    /// Create a new checkpoint store at the given directory.
    ///
    /// Creates the directory if it does not exist.
    ///
    /// # Errors
    ///
    /// Returns `RollbackError::Io` if the directory cannot be created.
    pub fn new(store_dir: impl AsRef<Path>) -> Result<Self, RollbackError> {
        let dir = store_dir.as_ref().to_path_buf();
        std::fs::create_dir_all(&dir)
            .map_err(|e| RollbackError::Io { path: dir.display().to_string(), source: e })?;
        let dir = dir
            .canonicalize()
            .map_err(|e| RollbackError::Io { path: dir.display().to_string(), source: e })?;
        Ok(Self { store_dir: dir })
    }

    /// Save a checkpoint to the store atomically.
    ///
    /// Uses the tempfile + rename pattern so a crash mid-write never
    /// corrupts an existing checkpoint file.
    ///
    /// # Errors
    ///
    /// Returns `RollbackError::Serialize` or `RollbackError::Io` on failure.
    pub fn save(&self, checkpoint: &RewriteCheckpoint) -> Result<PathBuf, RollbackError> {
        validate_checkpoint_id(&checkpoint.id)?;
        validate_checkpoint(checkpoint)?;
        let json = serde_json::to_string_pretty(checkpoint)
            .map_err(|e| RollbackError::Serialize(e.to_string()))?;
        let file_path = self.store_dir.join(format!("{}.json", checkpoint.id));

        let mut tmp = tempfile::NamedTempFile::new_in(&self.store_dir)
            .map_err(|e| RollbackError::Io { path: file_path.display().to_string(), source: e })?;
        tmp.write_all(json.as_bytes())
            .map_err(|e| RollbackError::Io { path: file_path.display().to_string(), source: e })?;
        tmp.flush()
            .map_err(|e| RollbackError::Io { path: file_path.display().to_string(), source: e })?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            tmp.as_file().set_permissions(std::fs::Permissions::from_mode(0o600)).map_err(|e| {
                RollbackError::Io { path: file_path.display().to_string(), source: e }
            })?;
        }
        tmp.as_file()
            .sync_all()
            .map_err(|e| RollbackError::Io { path: file_path.display().to_string(), source: e })?;
        tmp.persist(&file_path).map_err(|e| RollbackError::Io {
            path: file_path.display().to_string(),
            source: e.error,
        })?;
        std::fs::File::open(&self.store_dir).and_then(|directory| directory.sync_all()).map_err(
            |e| RollbackError::Io { path: self.store_dir.display().to_string(), source: e },
        )?;

        Ok(file_path)
    }

    /// Load a checkpoint from the store by ID.
    ///
    /// # Errors
    ///
    /// Returns `RollbackError::Io` if the file cannot be read, or
    /// `RollbackError::Deserialize` if it cannot be parsed.
    pub fn load(&self, id: &str) -> Result<RewriteCheckpoint, RollbackError> {
        validate_checkpoint_id(id)?;
        let file_path = self.store_dir.join(format!("{id}.json"));
        ensure_regular_store_entry(&file_path)?;
        let json = std::fs::read_to_string(&file_path)
            .map_err(|e| RollbackError::Io { path: file_path.display().to_string(), source: e })?;
        let checkpoint: RewriteCheckpoint =
            serde_json::from_str(&json).map_err(|e| RollbackError::Deserialize(e.to_string()))?;
        if checkpoint.id != id {
            return Err(RollbackError::IdentityMismatch {
                requested: id.to_string(),
                stored: checkpoint.id,
            });
        }
        validate_checkpoint(&checkpoint)?;
        Ok(checkpoint)
    }

    /// List all checkpoint IDs in the store.
    ///
    /// # Errors
    ///
    /// Returns `RollbackError::Io` if the store directory cannot be read.
    pub fn list(&self) -> Result<Vec<String>, RollbackError> {
        let mut ids = Vec::new();
        let entries = std::fs::read_dir(&self.store_dir).map_err(|e| RollbackError::Io {
            path: self.store_dir.display().to_string(),
            source: e,
        })?;
        for entry in entries {
            let entry = entry.map_err(|e| RollbackError::Io {
                path: self.store_dir.display().to_string(),
                source: e,
            })?;
            let path = entry.path();
            if path.extension().is_some_and(|ext| ext == "json") {
                ensure_regular_store_entry(&path)?;
                if let Some(name) = path.file_stem() {
                    let id = name.to_string_lossy().into_owned();
                    validate_checkpoint_id(&id)?;
                    ids.push(id);
                }
            }
        }
        ids.sort();
        Ok(ids)
    }

    /// Delete a checkpoint from the store.
    ///
    /// # Errors
    ///
    /// Returns `RollbackError::Io` if the file cannot be removed.
    pub fn delete(&self, id: &str) -> Result<(), RollbackError> {
        validate_checkpoint_id(id)?;
        let file_path = self.store_dir.join(format!("{id}.json"));
        ensure_regular_store_entry(&file_path)?;
        std::fs::remove_file(&file_path)
            .map_err(|e| RollbackError::Io { path: file_path.display().to_string(), source: e })?;
        std::fs::File::open(&self.store_dir).and_then(|directory| directory.sync_all()).map_err(
            |e| RollbackError::Io { path: self.store_dir.display().to_string(), source: e },
        )
    }
}

fn validate_checkpoint_id(id: &str) -> Result<(), RollbackError> {
    if id.is_empty()
        || id.len() > 128
        || !id.bytes().all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_'))
    {
        return Err(RollbackError::InvalidCheckpointId { id: id.to_string() });
    }
    Ok(())
}

fn ensure_regular_store_entry(path: &Path) -> Result<(), RollbackError> {
    let metadata = std::fs::symlink_metadata(path)
        .map_err(|e| RollbackError::Io { path: path.display().to_string(), source: e })?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
        return Err(RollbackError::UnsafeStoreEntry { path: path.display().to_string() });
    }
    Ok(())
}

/// Create a checkpoint from a list of file paths.
///
/// Reads each file, computes its SHA-256 hash, and stores a snapshot.
/// The checkpoint ID is derived from the current timestamp.
///
/// # Errors
///
/// Returns `RollbackError::Io` if any file cannot be read.
pub fn create_checkpoint(files: &[PathBuf]) -> Result<RewriteCheckpoint, RollbackError> {
    let mut snapshots = Vec::with_capacity(files.len());
    let mut seen = BTreeSet::new();

    for path in files {
        let canonical = path
            .canonicalize()
            .map_err(|e| RollbackError::Io { path: path.display().to_string(), source: e })?;
        if !seen.insert(canonical.clone()) {
            return Err(RollbackError::DuplicatePath { path: canonical.display().to_string() });
        }
        let contents = std::fs::read_to_string(&canonical)
            .map_err(|e| RollbackError::Io { path: canonical.display().to_string(), source: e })?;
        let hash = stable_sha256_hex(contents.as_bytes());
        snapshots.push(FileSnapshot { path: canonical, contents, hash });
    }

    // Generate a unique ID from hash of all file paths + a counter.
    let id = generate_checkpoint_id(&snapshots);

    Ok(RewriteCheckpoint {
        id,
        created_at: format!(
            "{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs()
        ),
        snapshots,
    })
}

/// Rollback files to their state at checkpoint time.
///
/// Writes each file's snapshot contents back to disk, then verifies that
/// the resulting file hash matches the checkpoint hash.
///
/// # Errors
///
/// Returns `RollbackError::Io` if a file cannot be written, or
/// `RollbackError::VerificationFailed` if the hash does not match after write.
pub fn rollback(checkpoint: &RewriteCheckpoint) -> Result<(), RollbackError> {
    validate_checkpoint(checkpoint)?;
    // Phase 1: Write all files atomically using the same permission-preserving,
    // fsyncing primitive as forward application.
    for snapshot in &checkpoint.snapshots {
        crate::file_io::write_source(&snapshot.path, &snapshot.contents).map_err(|error| {
            RollbackError::Io {
                path: snapshot.path.display().to_string(),
                source: std::io::Error::other(error.to_string()),
            }
        })?;
    }

    // Phase 2: Verify all files
    for snapshot in &checkpoint.snapshots {
        let actual_contents = std::fs::read_to_string(&snapshot.path).map_err(|e| {
            RollbackError::Io { path: snapshot.path.display().to_string(), source: e }
        })?;
        let actual_hash = stable_sha256_hex(actual_contents.as_bytes());
        if actual_hash != snapshot.hash {
            return Err(RollbackError::VerificationFailed {
                path: snapshot.path.display().to_string(),
                expected: snapshot.hash.clone(),
                actual: actual_hash,
            });
        }
    }

    Ok(())
}

/// Restore a checkpoint only while every target still has the caller's
/// expected post-rewrite digest. This is the transaction-safe rollback path:
/// it refuses to clobber edits made after our commit attempt.
pub(crate) fn rollback_if_unchanged(
    checkpoint: &RewriteCheckpoint,
    expected_current: &BTreeMap<PathBuf, String>,
) -> Result<(), RollbackError> {
    validate_checkpoint(checkpoint)?;
    for snapshot in &checkpoint.snapshots {
        let expected = expected_current.get(&snapshot.path).ok_or_else(|| {
            RollbackError::ConcurrentModification {
                path: snapshot.path.display().to_string(),
                expected: "<transaction-owned digest>".into(),
                actual: "<missing expectation>".into(),
            }
        })?;
        let actual = std::fs::read_to_string(&snapshot.path)
            .map(|contents| stable_sha256_hex(contents.as_bytes()))
            .unwrap_or_else(|_| "<unreadable>".into());
        if &actual != expected {
            return Err(RollbackError::ConcurrentModification {
                path: snapshot.path.display().to_string(),
                expected: expected.clone(),
                actual,
            });
        }
    }
    rollback(checkpoint)
}

fn validate_checkpoint(checkpoint: &RewriteCheckpoint) -> Result<(), RollbackError> {
    let mut seen = BTreeSet::new();
    for snapshot in &checkpoint.snapshots {
        if !seen.insert(snapshot.path.clone()) {
            return Err(RollbackError::DuplicatePath { path: snapshot.path.display().to_string() });
        }
        let actual = stable_sha256_hex(snapshot.contents.as_bytes());
        if actual != snapshot.hash {
            return Err(RollbackError::InvalidSnapshotHash {
                path: snapshot.path.display().to_string(),
                expected: snapshot.hash.clone(),
                actual,
            });
        }
    }
    Ok(())
}

/// Check whether any files have changed since the checkpoint was created.
///
/// Returns a map of changed file paths to their current hash.
/// Files that cannot be read are included with hash `"<unreadable>"`.
#[must_use]
pub fn changed_since_checkpoint(checkpoint: &RewriteCheckpoint) -> FxHashMap<PathBuf, String> {
    let mut changed = FxHashMap::default();
    for snapshot in &checkpoint.snapshots {
        match std::fs::read_to_string(&snapshot.path) {
            Ok(contents) => {
                let current_hash = stable_sha256_hex(contents.as_bytes());
                if current_hash != snapshot.hash {
                    changed.insert(snapshot.path.clone(), current_hash);
                }
            }
            Err(_) => {
                changed.insert(snapshot.path.clone(), "<unreadable>".into());
            }
        }
    }
    changed
}

/// Generate a checkpoint ID from the snapshots (deterministic for same input).
fn generate_checkpoint_id(snapshots: &[FileSnapshot]) -> String {
    let mut material = Vec::new();
    for snapshot in snapshots {
        material.extend_from_slice(snapshot.path.display().to_string().as_bytes());
        material.extend_from_slice(snapshot.hash.as_bytes());
    }
    // The id is a display handle, not evidence: it keeps the historical
    // leading-64-bit truncation of the digest so existing checkpoint
    // directories stay addressable.
    format!("ckpt-{}", &stable_sha256_hex(&material)[..16])
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    /// Create a unique, isolated temp directory for a test.
    /// Returns a `TempDir` that auto-cleans on drop -- no manual cleanup needed.
    fn isolated_temp_dir() -> tempfile::TempDir {
        tempfile::tempdir().expect("failed to create isolated temp dir")
    }

    fn write_test_file(dir: &Path, name: &str, content: &str) -> PathBuf {
        let path = dir.join(name);
        fs::write(&path, content).unwrap();
        path
    }

    // --- stable_sha256_hex tests ---

    #[test]
    fn test_sha256_hex_deterministic() {
        let h1 = stable_sha256_hex(b"hello world");
        let h2 = stable_sha256_hex(b"hello world");
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_sha256_hex_different_inputs() {
        let h1 = stable_sha256_hex(b"hello");
        let h2 = stable_sha256_hex(b"world");
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_sha256_hex_known_value() {
        // SHA-256 of empty string is well-known
        let hash = stable_sha256_hex(b"");
        assert_eq!(hash, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
    }

    // --- create_checkpoint tests ---

    #[test]
    fn test_create_checkpoint_single_file() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(dir.path(), "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(&[f1]).unwrap();
        assert_eq!(ckpt.file_count(), 1);
        assert!(!ckpt.is_empty());
        assert_eq!(ckpt.snapshots[0].contents, "fn a() {}\n");
        assert_eq!(ckpt.snapshots[0].hash, stable_sha256_hex(b"fn a() {}\n"));
    }

    #[test]
    fn test_create_checkpoint_multiple_files() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(dir.path(), "a.rs", "fn a() {}\n");
        let f2 = write_test_file(dir.path(), "b.rs", "fn b() {}\n");

        let ckpt = create_checkpoint(&[f1, f2]).unwrap();
        assert_eq!(ckpt.file_count(), 2);
    }

    #[test]
    fn test_create_checkpoint_empty_files_list() {
        let ckpt = create_checkpoint(&[]).unwrap();
        assert!(ckpt.is_empty());
        assert_eq!(ckpt.file_count(), 0);
    }

    #[test]
    fn test_create_checkpoint_nonexistent_file() {
        let result = create_checkpoint(&[PathBuf::from("/nonexistent/file.rs")]);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), RollbackError::Io { .. }));
    }

    #[test]
    fn test_checkpoint_get_snapshot() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(dir.path(), "x.rs", "fn x() {}\n");

        let ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();
        let snap = ckpt.get_snapshot(&f1);
        assert!(snap.is_some());
        assert_eq!(snap.unwrap().contents, "fn x() {}\n");

        assert!(ckpt.get_snapshot(Path::new("/no/such/file")).is_none());
    }

    // --- rollback tests ---

    #[test]
    fn test_rollback_restores_original_content() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(dir.path(), "a.rs", "fn original() {}\n");

        let ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();

        // Modify the file
        fs::write(&f1, "fn modified() {}\n").unwrap();
        assert_eq!(fs::read_to_string(&f1).unwrap(), "fn modified() {}\n");

        // Rollback
        rollback(&ckpt).unwrap();
        assert_eq!(fs::read_to_string(&f1).unwrap(), "fn original() {}\n");
    }

    #[test]
    fn test_rollback_multiple_files() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(dir.path(), "a.rs", "fn a() {}\n");
        let f2 = write_test_file(dir.path(), "b.rs", "fn b() {}\n");

        let ckpt = create_checkpoint(&[f1.clone(), f2.clone()]).unwrap();

        // Modify both
        fs::write(&f1, "fn a_changed() {}\n").unwrap();
        fs::write(&f2, "fn b_changed() {}\n").unwrap();

        rollback(&ckpt).unwrap();

        assert_eq!(fs::read_to_string(&f1).unwrap(), "fn a() {}\n");
        assert_eq!(fs::read_to_string(&f2).unwrap(), "fn b() {}\n");
    }

    #[test]
    fn test_rollback_idempotent() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(dir.path(), "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();

        // Rollback twice should be fine
        rollback(&ckpt).unwrap();
        rollback(&ckpt).unwrap();
        assert_eq!(fs::read_to_string(&f1).unwrap(), "fn a() {}\n");
    }

    #[test]
    fn conditional_rollback_refuses_later_external_edit() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(dir.path(), "a.rs", "fn original() {}\n");
        let ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();
        fs::write(&f1, "fn external() {}\n").unwrap();
        let expected = [(f1.canonicalize().unwrap(), stable_sha256_hex(b"fn transaction_owned() {}\n"))]
            .into_iter()
            .collect();

        assert!(matches!(
            rollback_if_unchanged(&ckpt, &expected),
            Err(RollbackError::ConcurrentModification { .. })
        ));
        assert_eq!(fs::read_to_string(&f1).unwrap(), "fn external() {}\n");
    }

    #[test]
    fn tampered_snapshot_is_rejected_before_rollback_writes() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(dir.path(), "a.rs", "fn original() {}\n");
        let mut ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();
        ckpt.snapshots[0].contents = "fn attacker() {}\n".into();
        fs::write(&f1, "fn current() {}\n").unwrap();

        assert!(matches!(rollback(&ckpt), Err(RollbackError::InvalidSnapshotHash { .. })));
        assert_eq!(fs::read_to_string(&f1).unwrap(), "fn current() {}\n");
    }

    // --- changed_since_checkpoint tests ---

    #[test]
    fn test_changed_since_no_changes() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(dir.path(), "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(&[f1]).unwrap();
        let changed = changed_since_checkpoint(&ckpt);
        assert!(changed.is_empty());
    }

    #[test]
    fn test_changed_since_with_modification() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(dir.path(), "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();
        let checkpoint_path = ckpt.snapshots[0].path.clone();

        fs::write(&f1, "fn a_changed() {}\n").unwrap();
        let changed = changed_since_checkpoint(&ckpt);
        assert_eq!(changed.len(), 1);
        assert!(changed.contains_key(&checkpoint_path));
    }

    #[test]
    fn test_changed_since_file_deleted() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(dir.path(), "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();
        let checkpoint_path = ckpt.snapshots[0].path.clone();

        fs::remove_file(&f1).unwrap();
        let changed = changed_since_checkpoint(&ckpt);
        assert_eq!(changed.len(), 1);
        assert_eq!(changed[&checkpoint_path], "<unreadable>");
    }

    // --- CheckpointStore tests ---

    #[test]
    fn test_store_save_and_load() {
        let dir = isolated_temp_dir();
        let store_dir = dir.path().join("checkpoints");
        let store = CheckpointStore::new(&store_dir).unwrap();

        let src_dir = dir.path().join("src");
        fs::create_dir_all(&src_dir).unwrap();
        let f1 = write_test_file(&src_dir, "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(&[f1]).unwrap();
        let saved_path = store.save(&ckpt).unwrap();
        assert!(saved_path.exists());

        let loaded = store.load(&ckpt.id).unwrap();
        assert_eq!(loaded.file_count(), 1);
        assert_eq!(loaded.snapshots[0].contents, "fn a() {}\n");
    }

    #[test]
    fn test_store_list() {
        let dir = isolated_temp_dir();
        let store_dir = dir.path().join("checkpoints");
        let store = CheckpointStore::new(&store_dir).unwrap();

        // Create and save two checkpoints
        let src_dir = dir.path().join("src");
        fs::create_dir_all(&src_dir).unwrap();
        let f1 = write_test_file(&src_dir, "a.rs", "fn a() {}\n");
        let f2 = write_test_file(&src_dir, "b.rs", "fn b() {}\n");

        let ckpt1 = create_checkpoint(&[f1]).unwrap();
        let ckpt2 = create_checkpoint(&[f2]).unwrap();
        store.save(&ckpt1).unwrap();
        store.save(&ckpt2).unwrap();

        let ids = store.list().unwrap();
        assert_eq!(ids.len(), 2);
    }

    #[test]
    fn test_store_delete() {
        let dir = isolated_temp_dir();
        let store_dir = dir.path().join("checkpoints");
        let store = CheckpointStore::new(&store_dir).unwrap();

        let src_dir = dir.path().join("src");
        fs::create_dir_all(&src_dir).unwrap();
        let f1 = write_test_file(&src_dir, "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(&[f1]).unwrap();
        store.save(&ckpt).unwrap();

        store.delete(&ckpt.id).unwrap();
        let ids = store.list().unwrap();
        assert!(ids.is_empty());
    }

    #[test]
    fn test_store_load_nonexistent() {
        let dir = isolated_temp_dir();
        let store = CheckpointStore::new(dir.path()).unwrap();
        let result = store.load("nonexistent-id");
        assert!(result.is_err());
    }

    #[test]
    fn checkpoint_store_rejects_traversal_ids() {
        let dir = isolated_temp_dir();
        let store = CheckpointStore::new(dir.path()).unwrap();
        for id in ["../escape", ".", "a/b", ""] {
            assert!(matches!(store.load(id), Err(RollbackError::InvalidCheckpointId { .. })));
            assert!(matches!(store.delete(id), Err(RollbackError::InvalidCheckpointId { .. })));
        }
    }

    #[cfg(unix)]
    #[test]
    fn checkpoint_store_rejects_symlink_entries() {
        use std::os::unix::fs::symlink;

        let dir = isolated_temp_dir();
        let store_dir = dir.path().join("store");
        let store = CheckpointStore::new(&store_dir).unwrap();
        let outside = dir.path().join("outside.json");
        fs::write(&outside, "{}").unwrap();
        symlink(&outside, store_dir.join("evil.json")).unwrap();

        assert!(matches!(store.load("evil"), Err(RollbackError::UnsafeStoreEntry { .. })));
        assert!(matches!(store.list(), Err(RollbackError::UnsafeStoreEntry { .. })));
    }

    #[cfg(unix)]
    #[test]
    fn checkpoint_store_files_are_owner_only() {
        use std::os::unix::fs::PermissionsExt;

        let dir = isolated_temp_dir();
        let store = CheckpointStore::new(dir.path().join("store")).unwrap();
        let source = write_test_file(dir.path(), "a.rs", "fn a() {}\n");
        let path = store.save(&create_checkpoint(&[source]).unwrap()).unwrap();
        assert_eq!(fs::metadata(path).unwrap().permissions().mode() & 0o777, 0o600);
    }

    // --- RewriteCheckpoint tests ---

    #[test]
    fn test_checkpoint_id_deterministic_for_same_input() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(dir.path(), "a.rs", "fn a() {}\n");

        let ckpt1 = create_checkpoint(std::slice::from_ref(&f1)).unwrap();
        let ckpt2 = create_checkpoint(&[f1]).unwrap();
        assert_eq!(ckpt1.id, ckpt2.id);
    }

    #[test]
    fn test_checkpoint_serialization_roundtrip() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(dir.path(), "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(&[f1]).unwrap();
        let json = serde_json::to_string(&ckpt).unwrap();
        let deserialized: RewriteCheckpoint = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized.id, ckpt.id);
        assert_eq!(deserialized.file_count(), ckpt.file_count());
    }

    // --- Integration: checkpoint + modify + rollback ---

    #[test]
    fn test_full_checkpoint_modify_rollback_cycle() {
        let dir = isolated_temp_dir();
        let f1 = write_test_file(
            dir.path(),
            "lib.rs",
            "pub fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n",
        );
        let f2 = write_test_file(dir.path(), "util.rs", "fn helper() -> bool { true }\n");

        // Step 1: Checkpoint
        let ckpt = create_checkpoint(&[f1.clone(), f2.clone()]).unwrap();
        assert_eq!(ckpt.file_count(), 2);
        assert!(changed_since_checkpoint(&ckpt).is_empty());

        // Step 2: Simulate rewrites
        fs::write(&f1, "#[requires(\"a + b < u64::MAX\")]\npub fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n").unwrap();
        fs::write(&f2, "#[ensures(\"result == true\")]\nfn helper() -> bool { true }\n").unwrap();

        // Step 3: Verify changes detected
        let changed = changed_since_checkpoint(&ckpt);
        assert_eq!(changed.len(), 2);

        // Step 4: Rollback
        rollback(&ckpt).unwrap();

        // Step 5: Verify restored
        assert_eq!(
            fs::read_to_string(&f1).unwrap(),
            "pub fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n"
        );
        assert_eq!(fs::read_to_string(&f2).unwrap(), "fn helper() -> bool { true }\n");
        assert!(changed_since_checkpoint(&ckpt).is_empty());
    }

    #[test]
    fn test_store_full_workflow() {
        let dir = isolated_temp_dir();
        let store_dir = dir.path().join(".trust-checkpoints");
        let store = CheckpointStore::new(&store_dir).unwrap();

        let f1 = write_test_file(dir.path(), "main.rs", "fn main() {}\n");

        // Save checkpoint
        let ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();
        store.save(&ckpt).unwrap();

        // Modify file
        fs::write(&f1, "fn main() { panic!() }\n").unwrap();

        // Load and rollback
        let ids = store.list().unwrap();
        let loaded = store.load(&ids[0]).unwrap();
        rollback(&loaded).unwrap();

        assert_eq!(fs::read_to_string(&f1).unwrap(), "fn main() {}\n");

        // Clean up checkpoint
        store.delete(&ids[0]).unwrap();
        assert!(store.list().unwrap().is_empty());
    }
}
