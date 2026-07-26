//! Helpers for materializing [`crate::CacheInputs`] from filesystem and
//! binary state.
//!
//! These are low-level primitives for experimental cache tooling. They do not
//! discover Cargo's complete build-input graph. Kept in `trust-buildcache` so
//! their deterministic byte-level behavior lives with the prototype schema:
//!
//! - source file hashing is deterministic by path + content;
//! - binary fingerprinting is SHA-256 of the file contents at a path;
//! - solver-version assembly is a sorted Vec of (name, version) pairs so
//!   ordering doesn't perturb the cache key.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use crate::error::{BuildCacheError, Result};

/// Hash a single file's bytes. SHA-256 over the file content; no path.
///
/// Missing or unreadable inputs are errors. Treating either as an all-zero
/// digest would collapse distinct I/O failures onto the same apparent input
/// identity and allow a key to be computed for bytes that were never read.
pub fn hash_file(path: &Path) -> Result<[u8; 32]> {
    let bytes = std::fs::read(path).map_err(|error| BuildCacheError::io(path, error))?;
    let mut hasher = Sha256::new();
    hasher.update(&bytes);
    let digest = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    Ok(out)
}

/// Hash a set of source files. Returns `(path, sha256)` sorted by path
/// so the resulting Vec is deterministic regardless of input order.
pub fn hash_sources<I, P>(paths: I) -> Result<Vec<(PathBuf, [u8; 32])>>
where
    I: IntoIterator<Item = P>,
    P: AsRef<Path>,
{
    let mut out: Vec<(PathBuf, [u8; 32])> = Vec::new();
    for p in paths {
        let p = p.as_ref().to_path_buf();
        let hash = hash_file(&p)?;
        out.push((p, hash));
    }
    out.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(out)
}

/// Fingerprint a binary by hashing its bytes.
pub fn fingerprint_binary(path: &Path) -> Result<String> {
    let bytes = std::fs::read(path).map_err(|e| BuildCacheError::io(path, e))?;
    let mut hasher = Sha256::new();
    hasher.update(&bytes);
    Ok(format!("{:x}", hasher.finalize()))
}

/// Normalize a list of `(name, version)` pairs into the canonical form
/// `CacheInputs` expects: sorted by name, no duplicates (last write
/// wins).
pub fn normalize_versions<I, S, V>(pairs: I) -> Vec<(String, String)>
where
    I: IntoIterator<Item = (S, V)>,
    S: Into<String>,
    V: Into<String>,
{
    let mut map: std::collections::BTreeMap<String, String> = std::collections::BTreeMap::new();
    for (name, version) in pairs {
        map.insert(name.into(), version.into());
    }
    map.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use tempfile::TempDir;

    use super::*;

    #[test]
    fn hash_file_is_deterministic() {
        let tmp = TempDir::new().unwrap();
        let p = tmp.path().join("a.rs");
        let mut f = std::fs::File::create(&p).unwrap();
        f.write_all(b"contents").unwrap();
        let h1 = hash_file(&p).unwrap();
        let h2 = hash_file(&p).unwrap();
        assert_eq!(h1, h2);
        assert_ne!(h1, [0u8; 32]);
    }

    #[test]
    fn hash_file_missing_fails_closed() {
        let tmp = TempDir::new().unwrap();
        let p = tmp.path().join("never-existed.rs");
        assert!(hash_file(&p).is_err());
    }

    #[test]
    fn hash_file_changes_with_content() {
        let tmp = TempDir::new().unwrap();
        let p = tmp.path().join("a.rs");
        std::fs::write(&p, b"v1").unwrap();
        let h1 = hash_file(&p).unwrap();
        std::fs::write(&p, b"v2").unwrap();
        let h2 = hash_file(&p).unwrap();
        assert_ne!(h1, h2);
    }

    #[test]
    fn hash_sources_is_sorted_by_path() {
        let tmp = TempDir::new().unwrap();
        let a = tmp.path().join("a.rs");
        let b = tmp.path().join("b.rs");
        let c = tmp.path().join("c.rs");
        for p in [&a, &b, &c] {
            std::fs::write(p, b"x").unwrap();
        }
        let out = hash_sources([c.clone(), a.clone(), b.clone()]).unwrap();
        assert_eq!(out.len(), 3);
        assert_eq!(out[0].0, a);
        assert_eq!(out[1].0, b);
        assert_eq!(out[2].0, c);
    }

    #[test]
    fn fingerprint_binary_changes_when_bytes_change() {
        let tmp = TempDir::new().unwrap();
        let p = tmp.path().join("binary");
        std::fs::write(&p, b"v1").unwrap();
        let f1 = fingerprint_binary(&p).unwrap();
        std::fs::write(&p, b"v2").unwrap();
        let f2 = fingerprint_binary(&p).unwrap();
        assert_ne!(f1, f2);
        assert_eq!(f1.len(), 64);
        assert_eq!(f2.len(), 64);
    }

    #[test]
    fn normalize_versions_sorts_and_dedups() {
        let raw = vec![("ay", "1.2.3"), ("trust-vc", "0.5.0"), ("ay", "1.2.4")];
        let out = normalize_versions(raw);
        assert_eq!(
            out,
            vec![
                ("ay".to_string(), "1.2.4".to_string()),
                ("trust-vc".to_string(), "0.5.0".to_string())
            ]
        );
    }
}
