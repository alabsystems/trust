//! Byte-compatible reader of the complete `seal-content-v1` identity.
//!
//! This binds every shipped file, directory and link, with the same four root
//! record exclusions and mode normalization as promotion. It never establishes
//! who wrote a provenance record or whether a build/receipt is admissible.

use std::collections::BTreeMap;
use std::fs;
use std::os::unix::fs::MetadataExt;
use std::path::Path;

use serde::{Deserialize, Serialize};
use trust_sha2::{Digest, Sha256};

use crate::tree::{self, Fingerprint};
use crate::{Result, refusal};

pub const SCOPE: &str = "seal-content-v1";
pub const RECORDS: &[&str] =
    &["PROVENANCE", "PROVENANCE.build-status", "SEED-MINT", "STAGE0-LINEAGE"];
const MODE_MASK: u32 = 0o7755;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Identity {
    pub sha256: String,
    pub files: u64,
    pub links: u64,
    pub directories: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub path: Vec<u8>,
    pub kind: u8,
    pub mode: String,
    pub value: Vec<u8>,
}

pub fn entries(root: &Path) -> Result<Vec<Entry>> {
    let root = fs::canonicalize(root)?;
    if !root.is_dir() {
        return Err(refusal("seal is not a directory"));
    }
    let before = tree::stats(&root, false, RECORDS)?;
    let mut inode_hashes = BTreeMap::<(u64, u64), (Fingerprint, String)>::new();
    let mut out = Vec::new();
    for relative in tree::entries(&root, false, RECORDS)? {
        let path = tree::no_link_ancestors(&root, &relative)?;
        let metadata = fs::symlink_metadata(&path)?;
        let mode = format!("{:04o}", metadata.mode() & MODE_MASK);
        let (kind, mode, value) = if metadata.file_type().is_dir() {
            (b'D', mode, Vec::new())
        } else if metadata.file_type().is_symlink() {
            (b'L', "-".into(), tree::path_bytes(&tree::read_link(&path)?))
        } else if metadata.file_type().is_file() {
            let stamp = Fingerprint::of(&metadata);
            let hash = match inode_hashes.get(&stamp.inode()) {
                Some((prior, hash)) if prior == &stamp => hash.clone(),
                Some(_) => {
                    return Err(refusal(format!(
                        "seal hard-link input changed: {}",
                        path.display()
                    )));
                }
                None => {
                    let hash = tree::hash_file(&path)?;
                    inode_hashes.insert(stamp.inode(), (stamp, hash.clone()));
                    hash
                }
            };
            (b'F', mode, hash.into_bytes())
        } else {
            return Err(refusal(format!(
                "seal entry is neither a regular file, a symlink nor a directory: {}",
                path.display()
            )));
        };
        out.push(Entry { path: tree::path_bytes(&relative), kind, mode, value });
    }
    if tree::stats(&root, false, RECORDS)? != before {
        return Err(refusal("complete seal tree changed while hashing"));
    }
    Ok(out)
}

pub fn identity(root: &Path) -> Result<Identity> {
    let mut digest = Sha256::new();
    let mut result = Identity { sha256: String::new(), files: 0, links: 0, directories: 0 };
    for entry in entries(root)? {
        for field in [&[entry.kind][..], entry.mode.as_bytes(), &entry.value, &entry.path] {
            digest.update(field);
            digest.update([0]);
        }
        match entry.kind {
            b'F' => result.files += 1,
            b'L' => result.links += 1,
            b'D' => result.directories += 1,
            _ => unreachable!(),
        }
    }
    result.sha256 = format!("{:x}", digest.finalize());
    Ok(result)
}

impl Identity {
    pub fn provenance_lines(&self, prefix: &str) -> Result<Vec<String>> {
        if prefix.is_empty() || !prefix.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'_') {
            return Err(refusal(
                "identity prefix must contain ASCII letters, digits or underscores",
            ));
        }
        Ok(vec![
            format!("{prefix}_sha256={}", self.sha256),
            format!("{prefix}_files={}", self.files),
            format!("{prefix}_links={}", self.links),
            format!("{prefix}_dirs={}", self.directories),
            format!("{prefix}_scope={SCOPE}"),
        ])
    }
}
