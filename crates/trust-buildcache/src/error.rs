//! BuildCacheError and Result type alias.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;

use thiserror::Error;

#[derive(Debug, Error)]
pub enum BuildCacheError {
    #[error("I/O error at {path}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },

    #[error("cache entry {key_hex} already exists but is incomplete or corrupt")]
    IncompleteEntry { key_hex: String },

    #[error("serialization error: {0}")]
    Serde(#[from] serde_json::Error),
}

pub type Result<T> = std::result::Result<T, BuildCacheError>;

impl BuildCacheError {
    pub(crate) fn io(path: impl Into<PathBuf>, source: std::io::Error) -> Self {
        Self::Io { path: path.into(), source }
    }
}
