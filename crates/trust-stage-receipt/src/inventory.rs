// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Bounded directory-content observations, never provenance or proof authority.
//!
//! Every descendant directory and regular file is recorded, without suffix
//! filtering. Unix capture rejects descendant links and special files, anchors traversal
//! to directory handles, and checks observed metadata again before returning.
//! Namespace parents must be trusted. These sequential observations are not an
//! immutable filesystem snapshot or protection against changes restored between
//! observations. Other platforms explicitly refuse this strict capture API.

use std::path::{Path, PathBuf};

use crate::Result;

/// Bounds for the accepted tree, including directory entries and path bytes.
/// Directory enumeration can temporarily retain up to `max_entries` names at
/// each active depth before charging the aggregate accepted-path byte budget.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub max_entries: usize,
    pub max_depth: usize,
    pub max_path_bytes: usize,
    pub max_total_path_bytes: usize,
    pub max_file_bytes: u64,
    pub max_total_bytes: u64,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_entries: 1024,
            max_depth: 16,
            max_path_bytes: 4096,
            max_total_path_bytes: 256 * 1024,
            max_file_bytes: 2 * 1024 * 1024 * 1024,
            max_total_bytes: 8 * 1024 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EntryKind {
    Directory,
    File { bytes: u64, sha256: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    relative_path: PathBuf,
    kind: EntryKind,
}

impl Entry {
    pub fn relative_path(&self) -> &Path {
        &self.relative_path
    }

    pub fn kind(&self) -> &EntryKind {
        &self.kind
    }
}

/// An observation of this directory tree; no deserializer or acceptance token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirectorySnapshot {
    root: PathBuf,
    entries: Vec<Entry>,
    total_bytes: u64,
}

impl DirectorySnapshot {
    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn entries(&self) -> &[Entry] {
        &self.entries
    }

    pub fn total_bytes(&self) -> u64 {
        self.total_bytes
    }
}

pub fn capture_directory(root: &Path, limits: Limits) -> Result<DirectorySnapshot> {
    #[cfg(unix)]
    return unix::capture(root, limits);
    #[cfg(not(unix))]
    {
        let _ = (root, limits);
        Err(crate::Refusal("strict directory inventory requires Unix no-follow handles".into()))
    }
}

#[cfg(unix)]
mod unix;

#[cfg(all(test, unix))]
mod tests;
