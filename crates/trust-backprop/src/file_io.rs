//! File I/O for trust-backprop: read source, apply rewrites, write modified files.
//!
//! Bridges the gap between the in-memory `RewriteEngine` and the filesystem.
//! Reads `.rs` source files, converts proposals into offset-aware rewrites via
//! `proposal_converter`, applies them via `RewriteEngine`, and writes results.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use trust_types::fx::FxHashMap;

use crate::proposal_converter::{ConvertError, convert_proposal};
use crate::rewriter::{RewriteEngine, RewriteError};
use crate::{RewritePlan, SourceRewrite};
use trust_strengthen::Proposal;

/// Errors from file-level rewrite operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum FileRewriteError {
    /// An I/O error reading or writing a file.
    #[error("I/O error on `{path}`: {source}")]
    Io { path: String, source: std::io::Error },
    /// A proposal conversion error (function not found, etc.).
    #[error(transparent)]
    Convert(#[from] ConvertError),
    /// A rewrite engine error (offset mismatch, etc.).
    #[error(transparent)]
    Rewrite(#[from] RewriteError),
    /// A rewrite target path is not a safe source file under the requested root.
    #[error("unsafe rewrite path `{path}`: {reason}")]
    UnsafePath { path: String, reason: String },
    /// A rewritten file failed structural AST validation during preflight.
    #[error("AST validation failed for `{path}`: {errors:?}")]
    AstValidation { path: String, errors: Vec<String> },
    /// Checkpoint creation or rollback failed.
    #[error("rollback/checkpoint error: {0}")]
    Rollback(#[from] crate::RollbackError),
    /// A multi-file commit failed; all previously written files were rolled back.
    #[error("commit failed while writing `{path}`: {reason}; rollback error: {rollback_error:?}")]
    CommitFailed { path: String, reason: String, rollback_error: Option<String> },
}

/// Result of applying rewrites to a single file.
#[derive(Debug)]
pub struct FileRewriteResult {
    /// The file path that was rewritten.
    pub path: String,
    /// The original source text.
    pub original: String,
    /// The modified source text.
    pub modified: String,
    /// Number of rewrites applied.
    pub rewrite_count: usize,
}

/// Read a source file from disk.
///
/// # Errors
///
/// Returns `FileRewriteError::Io` if the file cannot be read.
pub fn read_source(path: impl AsRef<Path>) -> Result<String, FileRewriteError> {
    let path_ref = path.as_ref();
    std::fs::read_to_string(path_ref)
        .map_err(|e| FileRewriteError::Io { path: path_ref.display().to_string(), source: e })
}

/// Write modified source back to disk atomically.
///
/// Uses the tempfile + rename pattern to prevent partial writes: content is
/// written to a temporary file in the same directory as the target, then
/// atomically renamed into place. If the process crashes mid-write, the
/// original file remains intact.
///
/// # Errors
///
/// Returns `FileRewriteError::Io` if the file cannot be written.
pub fn write_source(path: impl AsRef<Path>, content: &str) -> Result<(), FileRewriteError> {
    let path_ref = path.as_ref();
    let parent = path_ref.parent().unwrap_or(Path::new("."));

    let original_permissions =
        std::fs::metadata(path_ref).ok().map(|metadata| metadata.permissions());

    // Create temp file in the same directory to ensure same-filesystem rename.
    let mut tmp = tempfile::NamedTempFile::new_in(parent)
        .map_err(|e| FileRewriteError::Io { path: path_ref.display().to_string(), source: e })?;

    tmp.write_all(content.as_bytes())
        .map_err(|e| FileRewriteError::Io { path: path_ref.display().to_string(), source: e })?;

    tmp.flush()
        .map_err(|e| FileRewriteError::Io { path: path_ref.display().to_string(), source: e })?;
    if let Some(permissions) = original_permissions {
        tmp.as_file().set_permissions(permissions).map_err(|source| FileRewriteError::Io {
            path: path_ref.display().to_string(),
            source,
        })?;
    }
    tmp.as_file()
        .sync_all()
        .map_err(|source| FileRewriteError::Io { path: path_ref.display().to_string(), source })?;

    // Atomic rename into the target path.
    tmp.persist(path_ref).map_err(|e| FileRewriteError::Io {
        path: path_ref.display().to_string(),
        source: e.error,
    })?;

    // Persist the directory entry as well as the file data.
    std::fs::File::open(parent)
        .and_then(|directory| directory.sync_all())
        .map_err(|source| FileRewriteError::Io { path: parent.display().to_string(), source })?;

    Ok(())
}

/// Convert proposals into a `RewritePlan` with real byte offsets by reading source files.
///
/// Groups proposals by file, reads each file, locates functions, and produces
/// a sorted `RewritePlan` ready for application.
///
/// # Errors
///
/// Returns `FileRewriteError::Io` if a source file cannot be read.
/// Returns `FileRewriteError::Convert` if a function cannot be located.
pub fn proposals_to_plan(
    proposals: &[Proposal],
    source_root: impl AsRef<Path>,
) -> Result<RewritePlan, FileRewriteError> {
    let root = source_root.as_ref();
    let mut plan = RewritePlan::new(format!("File-aware plan: {} proposals", proposals.len()));

    // Cache source contents by file path to avoid re-reading
    let mut source_cache: FxHashMap<String, String> = FxHashMap::default();

    for proposal in proposals {
        let file_path_str = &proposal.function_path;
        let full_path = eligible_source_path(root, file_path_str)?;
        let full_path_str = full_path.display().to_string();

        // Read source if not cached
        if !source_cache.contains_key(file_path_str) {
            let source = read_source(&full_path)?;
            source_cache.insert(file_path_str.clone(), source);
        }

        let source = source_cache
            .get(file_path_str)
            // SAFETY: We just inserted into source_cache above.
            .unwrap_or_else(|| unreachable!("key missing from cache after insertion"));

        let rewrites = convert_proposal(proposal, source, &full_path_str)?;
        plan.rewrites.extend(rewrites);
    }

    plan.sort_for_application();
    Ok(plan)
}

fn eligible_source_path(root: &Path, file_path: &str) -> Result<PathBuf, FileRewriteError> {
    if let Some(reason) = crate::report_only_provenance_path_reason(file_path) {
        return Err(FileRewriteError::UnsafePath {
            path: file_path.to_owned(),
            reason: reason.into(),
        });
    }

    let requested = Path::new(file_path);
    if requested.is_absolute() {
        return Err(FileRewriteError::UnsafePath {
            path: file_path.to_owned(),
            reason:
                "absolute rewrite paths must be supplied through a source-root relative proposal"
                    .into(),
        });
    }
    if requested.components().any(|component| matches!(component, std::path::Component::ParentDir))
    {
        return Err(FileRewriteError::UnsafePath {
            path: file_path.to_owned(),
            reason: "rewrite paths may not escape the source root".into(),
        });
    }
    if requested.extension().and_then(|ext| ext.to_str()) != Some("rs") {
        return Err(FileRewriteError::UnsafePath {
            path: file_path.to_owned(),
            reason: "rewrite targets must be Rust source files".into(),
        });
    }

    let full_path = root.join(requested);
    let canonical_root = root
        .canonicalize()
        .map_err(|source| FileRewriteError::Io { path: root.display().to_string(), source })?;
    let canonical_full = full_path
        .canonicalize()
        .map_err(|source| FileRewriteError::Io { path: full_path.display().to_string(), source })?;
    if !canonical_full.starts_with(&canonical_root) {
        return Err(FileRewriteError::UnsafePath {
            path: file_path.to_owned(),
            reason: "canonical path is outside the source root".into(),
        });
    }

    Ok(canonical_full)
}

/// Apply a `RewritePlan` to files on disk, returning results for each modified file.
///
/// Groups rewrites by file, reads each file, applies all rewrites (in descending
/// offset order), and writes the result back. Returns a `FileRewriteResult` per file.
///
/// # Errors
///
/// Returns `FileRewriteError::Io` on read/write failures.
/// Returns `FileRewriteError::Rewrite` on rewrite engine failures.
pub fn apply_plan_to_files(plan: &RewritePlan) -> Result<Vec<FileRewriteResult>, FileRewriteError> {
    apply_plan_to_files_with_writer(plan, |path, content| write_source(path, content))
}

fn apply_plan_to_files_with_writer(
    plan: &RewritePlan,
    mut writer: impl FnMut(&Path, &str) -> Result<(), FileRewriteError>,
) -> Result<Vec<FileRewriteResult>, FileRewriteError> {
    let engine = RewriteEngine::new();

    // BTreeMap gives deterministic preflight and commit order independent of
    // hash seeding or the caller's plan ordering.
    let mut by_file: BTreeMap<String, Vec<&SourceRewrite>> = BTreeMap::new();
    for rewrite in &plan.rewrites {
        ensure_plan_rewrite_path(&rewrite.file_path)?;
        by_file.entry(rewrite.file_path.clone()).or_default().push(rewrite);
    }

    // Phase 1: read, source-bind, apply, and AST-validate every file. No writes
    // occur until the complete multi-file plan has passed.
    let mut prepared = Vec::new();
    for (file_path, rewrites) in &mut by_file {
        let original = read_source(file_path)?;
        let actual_hash = trust_types::stable_sha256_hex(original.as_bytes());
        for rewrite in rewrites.iter() {
            let Some(expected) = &rewrite.expected_source_hash else {
                return Err(RewriteError::UnboundPlan { file_path: file_path.clone() }.into());
            };
            if expected != &actual_hash {
                return Err(RewriteError::StalePlan {
                    file_path: file_path.clone(),
                    expected: expected.clone(),
                    actual: actual_hash.clone(),
                }
                .into());
            }
        }
        rewrites.sort_by(|left, right| right.offset.cmp(&left.offset));
        let bound_plan = RewritePlan {
            rewrites: rewrites.iter().map(|rewrite| (*rewrite).clone()).collect(),
            summary: format!("preflight {file_path}"),
        };
        let modified = engine.apply_plan_to_source(&original, &bound_plan)?;
        let validation = crate::validate_rewrite_ast(&original, &modified);
        if !validation.used_ast || !validation.passed {
            return Err(FileRewriteError::AstValidation {
                path: file_path.clone(),
                errors: validation.errors.iter().map(|error| format!("{error:?}")).collect(),
            });
        }
        prepared.push(FileRewriteResult {
            path: file_path.clone(),
            original,
            modified,
            rewrite_count: rewrites.len(),
        });
    }

    let paths = prepared.iter().map(|file| PathBuf::from(&file.path)).collect::<Vec<_>>();
    let checkpoint = crate::create_checkpoint(&paths)?;

    // Checkpoint creation is a second read. Bind it back to preflight so an
    // edit in that window is a stale-plan failure, never a new baseline that
    // we silently overwrite.
    for (file, snapshot) in prepared.iter().zip(&checkpoint.snapshots) {
        let expected = trust_types::stable_sha256_hex(file.original.as_bytes());
        if snapshot.hash != expected {
            return Err(RewriteError::StalePlan {
                file_path: file.path.clone(),
                expected,
                actual: snapshot.hash.clone(),
            }
            .into());
        }
    }

    // Phase 2: commit deterministically. If any write fails, restore the exact
    // subset this transaction actually wrote. Conditional rollback refuses to
    // clobber a later external edit.
    let mut committed = Vec::new();
    for (index, (file, snapshot)) in prepared.iter().zip(&checkpoint.snapshots).enumerate() {
        let before_hash = match current_file_hash(&snapshot.path) {
            Ok(hash) => hash,
            Err(error) => {
                let rollback_error = rollback_owned_subset(&checkpoint, &prepared, &committed);
                return Err(FileRewriteError::CommitFailed {
                    path: file.path.clone(),
                    reason: error.to_string(),
                    rollback_error,
                });
            }
        };
        if before_hash != snapshot.hash {
            let rollback_error = rollback_owned_subset(&checkpoint, &prepared, &committed);
            return Err(FileRewriteError::CommitFailed {
                path: file.path.clone(),
                reason: format!(
                    "source changed after preflight: expected {}, got {before_hash}",
                    snapshot.hash
                ),
                rollback_error,
            });
        }

        if let Err(error) = writer(&snapshot.path, &file.modified) {
            // An atomic writer may have persisted content and then failed its
            // directory fsync. Treat the current file as transaction-owned only
            // when its exact intended digest is present.
            if current_file_hash(&snapshot.path).ok().as_deref()
                == Some(trust_types::stable_sha256_hex(file.modified.as_bytes()).as_str())
            {
                committed.push(index);
            }
            let rollback_error = rollback_owned_subset(&checkpoint, &prepared, &committed);
            return Err(FileRewriteError::CommitFailed {
                path: file.path.clone(),
                reason: error.to_string(),
                rollback_error,
            });
        }

        // The writer reported success, so include this file in any rollback.
        // Conditional digest checks below decide whether it is still ours.
        committed.push(index);
        let expected_modified = trust_types::stable_sha256_hex(file.modified.as_bytes());
        let actual_modified = match current_file_hash(&snapshot.path) {
            Ok(hash) => hash,
            Err(error) => {
                let rollback_error = rollback_owned_subset(&checkpoint, &prepared, &committed);
                return Err(FileRewriteError::CommitFailed {
                    path: file.path.clone(),
                    reason: error.to_string(),
                    rollback_error,
                });
            }
        };
        if actual_modified != expected_modified {
            let rollback_error = rollback_owned_subset(&checkpoint, &prepared, &committed);
            return Err(FileRewriteError::CommitFailed {
                path: file.path.clone(),
                reason: format!(
                    "post-write verification failed: expected {expected_modified}, got {actual_modified}"
                ),
                rollback_error,
            });
        }
    }

    Ok(prepared)
}

fn current_file_hash(path: &Path) -> Result<String, FileRewriteError> {
    read_source(path).map(|source| trust_types::stable_sha256_hex(source.as_bytes()))
}

fn rollback_owned_subset(
    checkpoint: &crate::RewriteCheckpoint,
    prepared: &[FileRewriteResult],
    committed: &[usize],
) -> Option<String> {
    if committed.is_empty() {
        return None;
    }
    let mut snapshots = Vec::new();
    let mut expected = BTreeMap::new();
    let mut conflicts = Vec::new();
    for index in committed {
        let snapshot = &checkpoint.snapshots[*index];
        let intended = trust_types::stable_sha256_hex(prepared[*index].modified.as_bytes());
        match current_file_hash(&snapshot.path) {
            Ok(actual) if actual == intended => {
                snapshots.push(snapshot.clone());
                expected.insert(snapshot.path.clone(), intended);
            }
            Ok(actual) => conflicts.push(format!(
                "rollback refused concurrent modification of `{}`: expected {intended}, got {actual}",
                snapshot.path.display()
            )),
            Err(error) => conflicts.push(error.to_string()),
        }
    }
    if snapshots.is_empty() {
        return (!conflicts.is_empty()).then(|| conflicts.join("; "));
    }
    let subset = crate::RewriteCheckpoint {
        id: format!("{}-partial", checkpoint.id),
        created_at: checkpoint.created_at.clone(),
        snapshots,
    };
    if let Err(error) = crate::rollback::rollback_if_unchanged(&subset, &expected) {
        conflicts.push(error.to_string());
    }
    (!conflicts.is_empty()).then(|| conflicts.join("; "))
}

fn ensure_plan_rewrite_path(file_path: &str) -> Result<(), FileRewriteError> {
    if let Some(reason) = crate::report_only_provenance_path_reason(file_path) {
        return Err(FileRewriteError::UnsafePath {
            path: file_path.to_owned(),
            reason: reason.into(),
        });
    }
    if Path::new(file_path).extension().and_then(|ext| ext.to_str()) != Some("rs") {
        return Err(FileRewriteError::UnsafePath {
            path: file_path.to_owned(),
            reason: "rewrite targets must be Rust source files".into(),
        });
    }
    Ok(())
}

/// Apply a rewrite plan to source text in memory (no file I/O).
///
/// Convenience wrapper around `RewriteEngine::apply_plan_to_source` for callers
/// that already have the source in memory.
///
/// # Errors
///
/// Returns `RewriteError` on rewrite failures (wrapped in `FileRewriteError`).
pub fn apply_plan_to_source(source: &str, plan: &RewritePlan) -> Result<String, FileRewriteError> {
    let engine = RewriteEngine::new();
    Ok(engine.apply_plan_to_source(source, plan)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ClaimProvenance, RewriteKind, SourceRewrite};

    /// Create a unique, isolated temp directory for a test.
    /// Returns a `TempDir` that auto-cleans on drop -- no manual cleanup needed.
    fn isolated_temp_dir() -> tempfile::TempDir {
        tempfile::tempdir().expect("failed to create isolated temp dir")
    }

    #[test]
    fn test_read_source_success() {
        let dir = isolated_temp_dir();
        let file = dir.path().join("test_read.rs");
        std::fs::write(&file, "fn main() {}\n").unwrap();

        let content = read_source(&file).unwrap();
        assert_eq!(content, "fn main() {}\n");
    }

    #[test]
    fn test_read_source_not_found() {
        let result = read_source("/nonexistent/path/test.rs");
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), FileRewriteError::Io { .. }));
    }

    #[test]
    fn test_write_source_success() {
        let dir = isolated_temp_dir();
        let file = dir.path().join("test_write.rs");

        write_source(&file, "fn modified() {}\n").unwrap();

        let content = std::fs::read_to_string(&file).unwrap();
        assert_eq!(content, "fn modified() {}\n");
    }

    #[test]
    fn test_write_source_creates_file() {
        let dir = isolated_temp_dir();
        let file = dir.path().join("new_file.rs");

        write_source(&file, "fn new() {}\n").unwrap();
        assert!(file.exists());
    }

    #[cfg(unix)]
    #[test]
    fn test_write_source_preserves_permissions() {
        use std::os::unix::fs::PermissionsExt;

        let dir = isolated_temp_dir();
        let file = dir.path().join("executable.rs");
        std::fs::write(&file, "fn before() {}\n").unwrap();
        std::fs::set_permissions(&file, std::fs::Permissions::from_mode(0o744)).unwrap();
        write_source(&file, "fn after() {}\n").unwrap();
        assert_eq!(std::fs::metadata(&file).unwrap().permissions().mode() & 0o777, 0o744);
    }

    #[test]
    fn test_apply_plan_to_files_roundtrip() {
        let dir = isolated_temp_dir();
        let file = dir.path().join("roundtrip.rs");
        let source = "fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n";
        std::fs::write(&file, source).unwrap();

        let file_str = file.display().to_string();
        let mut plan = RewritePlan::new("roundtrip test");
        plan.rewrites.push(SourceRewrite {
            file_path: file_str.clone(),
            offset: 0,
            kind: RewriteKind::InsertAttribute {
                attribute: "#[requires(\"a + b < u64::MAX\")]".into(),
            },
            function_name: "get_midpoint".into(),
            rationale: "test".into(),
            expected_source_hash: Some(trust_types::stable_sha256_hex(source.as_bytes())),
            provenance: ClaimProvenance::Authoritative,
        });
        plan.sort_for_application();

        let results = apply_plan_to_files(&plan).unwrap();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].rewrite_count, 1);

        // Verify the file on disk was modified
        let on_disk = std::fs::read_to_string(&file).unwrap();
        assert!(on_disk.contains("#[requires(\"a + b < u64::MAX\")]"));
        assert!(on_disk.contains("fn get_midpoint"));
    }

    #[test]
    fn stale_plan_is_rejected_before_any_write() {
        let dir = isolated_temp_dir();
        let file = dir.path().join("stale.rs");
        let original = "fn f() {}\n";
        std::fs::write(&file, original).unwrap();
        let mut plan = RewritePlan::new("stale");
        plan.rewrites.push(SourceRewrite {
            file_path: file.display().to_string(),
            offset: 0,
            kind: RewriteKind::InsertAttribute { attribute: "#[trust::requires(true)]".into() },
            function_name: "f".into(),
            rationale: "test".into(),
            expected_source_hash: Some(trust_types::stable_sha256_hex(original.as_bytes())),
            provenance: ClaimProvenance::Authoritative,
        });
        let changed = "// concurrent edit\nfn f() {}\n";
        std::fs::write(&file, changed).unwrap();

        assert!(matches!(
            apply_plan_to_files(&plan),
            Err(FileRewriteError::Rewrite(RewriteError::StalePlan { .. }))
        ));
        assert_eq!(std::fs::read_to_string(&file).unwrap(), changed);
    }

    #[test]
    fn second_file_commit_failure_rolls_back_first_file() {
        let dir = isolated_temp_dir();
        let first = dir.path().join("a.rs");
        let second = dir.path().join("b.rs");
        let first_source = "fn a() {}\n";
        let second_source = "fn b() {}\n";
        std::fs::write(&first, first_source).unwrap();
        std::fs::write(&second, second_source).unwrap();
        let mut plan = RewritePlan::new("two files");
        for (path, source, name) in [(&first, first_source, "a"), (&second, second_source, "b")] {
            plan.rewrites.push(SourceRewrite {
                file_path: path.display().to_string(),
                offset: 0,
                kind: RewriteKind::InsertAttribute { attribute: "#[trust::requires(true)]".into() },
                function_name: name.into(),
                rationale: "test".into(),
                expected_source_hash: Some(trust_types::stable_sha256_hex(source.as_bytes())),
                provenance: ClaimProvenance::Authoritative,
            });
        }
        let mut writes = 0;
        let result = apply_plan_to_files_with_writer(&plan, |path, content| {
            writes += 1;
            if writes == 2 {
                return Err(FileRewriteError::Io {
                    path: path.display().to_string(),
                    source: std::io::Error::other("injected second-file failure"),
                });
            }
            write_source(path, content)
        });

        assert!(matches!(result, Err(FileRewriteError::CommitFailed { .. })));
        assert_eq!(std::fs::read_to_string(&first).unwrap(), first_source);
        assert_eq!(std::fs::read_to_string(&second).unwrap(), second_source);
    }

    #[test]
    fn failed_commit_preserves_concurrent_edit_to_unowned_file() {
        let dir = isolated_temp_dir();
        let first = dir.path().join("a.rs");
        let second = dir.path().join("b.rs");
        let first_source = "fn a() {}\n";
        let second_source = "fn b() {}\n";
        let external = "// external edit\nfn b() {}\n";
        std::fs::write(&first, first_source).unwrap();
        std::fs::write(&second, second_source).unwrap();
        let mut plan = RewritePlan::new("two files with race");
        for (path, source, name) in [(&first, first_source, "a"), (&second, second_source, "b")] {
            plan.rewrites.push(SourceRewrite {
                file_path: path.display().to_string(),
                offset: 0,
                kind: RewriteKind::InsertAttribute { attribute: "#[trust::requires(true)]".into() },
                function_name: name.into(),
                rationale: "test".into(),
                expected_source_hash: Some(trust_types::stable_sha256_hex(source.as_bytes())),
                provenance: ClaimProvenance::Authoritative,
            });
        }
        let mut writes = 0;
        let result = apply_plan_to_files_with_writer(&plan, |path, content| {
            writes += 1;
            if writes == 2 {
                std::fs::write(path, external).unwrap();
                return Err(FileRewriteError::Io {
                    path: path.display().to_string(),
                    source: std::io::Error::other("injected concurrent second-file edit"),
                });
            }
            write_source(path, content)
        });

        assert!(matches!(result, Err(FileRewriteError::CommitFailed { .. })));
        assert_eq!(std::fs::read_to_string(&first).unwrap(), first_source);
        assert_eq!(std::fs::read_to_string(&second).unwrap(), external);
    }

    #[test]
    fn test_apply_plan_to_files_rejects_binary_pseudo_path_without_writing_source_file() {
        let dir = isolated_temp_dir();
        let file = dir.path().join("mixed.rs");
        let source = "fn mapped(arg0: u64) -> u64 {\n    arg0\n}\n";
        std::fs::write(&file, source).unwrap();

        let file_str = file.display().to_string();
        let mut plan = RewritePlan::new("mixed source and report-only binary plan");
        plan.rewrites.push(SourceRewrite {
            file_path: file_str.clone(),
            offset: 0,
            kind: RewriteKind::InsertAttribute { attribute: "#[requires(\"arg0 > 0\")]".into() },
            function_name: "mapped".into(),
            rationale: "valid source rewrite must not be applied after binary pseudo-path".into(),
            expected_source_hash: Some(trust_types::stable_sha256_hex(source.as_bytes())),
            provenance: ClaimProvenance::Authoritative,
        });
        plan.rewrites.push(SourceRewrite {
            file_path: "binary:0x401000".into(),
            offset: 0,
            kind: RewriteKind::InsertAttribute { attribute: "#[requires(\"arg0 != 0\")]".into() },
            function_name: "recovered_entry".into(),
            rationale: "address-only binary provenance remains report-only".into(),
            expected_source_hash: None,
            provenance: ClaimProvenance::Authoritative,
        });

        let err = apply_plan_to_files(&plan)
            .expect_err("binary pseudo-path rewrites must fail before any file write");

        match err {
            FileRewriteError::UnsafePath { path, reason } => {
                assert_eq!(path, "binary:0x401000");
                assert!(reason.contains("binary pseudo-paths"));
                assert!(reason.contains("cannot be rewritten"));
            }
            other => panic!("expected UnsafePath for binary pseudo-path, got {other:?}"),
        }
        assert_eq!(std::fs::read_to_string(&file).unwrap(), source);
    }

    #[test]
    fn test_apply_plan_to_source_in_memory() {
        let source = "fn foo() {}\n";
        let mut plan = RewritePlan::new("in-memory test");
        plan.rewrites.push(SourceRewrite {
            file_path: "test.rs".into(),
            offset: 0,
            kind: RewriteKind::InsertAttribute { attribute: "#[ensures(\"true\")]".into() },
            function_name: "foo".into(),
            rationale: "test".into(),
            expected_source_hash: Some(trust_types::stable_sha256_hex(source.as_bytes())),
            provenance: ClaimProvenance::Authoritative,
        });

        let result = apply_plan_to_source(source, &plan).unwrap();
        assert!(result.contains("#[ensures(\"true\")]"));
        assert!(result.contains("fn foo()"));
    }

    #[test]
    fn test_proposals_to_plan_with_real_file() {
        let dir = isolated_temp_dir();

        // Create a source file at the path matching proposal.function_path
        let src_dir = dir.path().join("src");
        std::fs::create_dir_all(&src_dir).unwrap();
        let file = src_dir.join("lib.rs");
        std::fs::write(&file, "pub fn compute(x: u64) -> u64 {\n    x * 2\n}\n").unwrap();

        let proposal = Proposal {
            function_path: "src/lib.rs".into(),
            function_name: "compute".into(),
            kind: trust_strengthen::ProposalKind::AddPrecondition {
                spec_body: "x < 9223372036854775807".into(),
            },
            confidence: 0.9,
            rationale: "overflow".into(),
        };

        let plan = proposals_to_plan(&[proposal], dir.path()).unwrap();
        assert_eq!(plan.len(), 1);
        assert!(matches!(
            &plan.rewrites[0].kind,
            RewriteKind::InsertContractClause { clause: crate::ContractClauseKind::Requires, .. }
        ));
    }

    #[test]
    fn test_proposals_to_plan_file_not_found() {
        let dir = isolated_temp_dir();

        let proposal = Proposal {
            function_path: "nonexistent.rs".into(),
            function_name: "foo".into(),
            kind: trust_strengthen::ProposalKind::AddPrecondition { spec_body: "true".into() },
            confidence: 0.9,
            rationale: "test".into(),
        };

        let result = proposals_to_plan(&[proposal], dir.path());
        assert!(result.is_err());
    }

    #[test]
    fn test_proposals_to_plan_rejects_binary_address_only_before_backprop() {
        let dir = isolated_temp_dir();
        let proposal = Proposal {
            function_path: "binary:0x401000".into(),
            function_name: "decompiled_entry".into(),
            kind: trust_strengthen::ProposalKind::AddPrecondition { spec_body: "arg0 != 0".into() },
            confidence: 0.9,
            rationale: "binary-derived TrustIr lacks exact source provenance".into(),
        };

        let err = proposals_to_plan(&[proposal], dir.path())
            .expect_err("address-only binary provenance must be rejected before backprop");

        match err {
            FileRewriteError::UnsafePath { path, reason } => {
                assert_eq!(path, "binary:0x401000");
                assert!(reason.contains("binary pseudo-paths"));
                assert!(reason.contains("cannot be rewritten"));
            }
            other => {
                panic!("expected UnsafePath for missing exact binary provenance, got {other:?}")
            }
        }
    }

    #[test]
    fn test_proposals_to_plan_rejects_symbolic_pseudo_path_even_if_file_exists() {
        let dir = isolated_temp_dir();
        let pseudo_file = dir.path().join("crate::recovered.rs");
        std::fs::write(&pseudo_file, "fn recovered(x: u64) -> u64 {\n    x\n}\n").unwrap();
        let proposal = Proposal {
            function_path: "crate::recovered.rs".into(),
            function_name: "recovered".into(),
            kind: trust_strengthen::ProposalKind::AddPrecondition { spec_body: "x > 0".into() },
            confidence: 0.9,
            rationale: "symbolic def-path provenance is report-only".into(),
        };

        let err = proposals_to_plan(&[proposal], dir.path())
            .expect_err("symbolic pseudo-paths must be rejected before rewrite planning");

        match err {
            FileRewriteError::UnsafePath { path, reason } => {
                assert_eq!(path, "crate::recovered.rs");
                assert!(reason.contains("pseudo provenance paths"));
                assert!(reason.contains("cannot be rewritten"));
            }
            other => panic!("expected UnsafePath for symbolic pseudo-path, got {other:?}"),
        }
    }

    #[test]
    fn test_file_rewrite_result_fields() {
        let result = FileRewriteResult {
            path: "test.rs".into(),
            original: "fn foo() {}".into(),
            modified: "#[requires(\"true\")]\nfn foo() {}".into(),
            rewrite_count: 1,
        };
        assert_eq!(result.path, "test.rs");
        assert_ne!(result.original, result.modified);
        assert_eq!(result.rewrite_count, 1);
    }
}
