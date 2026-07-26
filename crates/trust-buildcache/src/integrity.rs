//! HMAC-SHA256 integrity seal for cache entries.
//!
//! Each stored entry carries an HMAC computed over the concatenation of
//! every artifact byte (rlib, rmeta, depfile, certificate.json) plus the
//! metadata JSON. The compatibility key is a format-versioned, non-secret
//! constant so every Trust tool can read entries written by another executable.
//!
//! Why: a `BuildCache` directory is just files on disk. The tag detects
//! accidental corruption and unsynchronized writes. Its key is derived on the
//! public, so it is not a security boundary against a writer with filesystem
//! access and cannot make a cached certificate evidentiary.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::Read as _;
use std::path::Path;

use hmac::{Hmac, Mac as _};
use sha2::{Digest as _, Sha256};

use crate::error::{BuildCacheError, Result};

const HMAC_FILENAME: &str = "hmac.hex";
const SEALED_FILES: &[&str] = &["rlib", "rmeta", "depfile", "certificate.json", "metadata.json"];
type HmacSha256 = Hmac<Sha256>;

fn compatibility_key() -> [u8; 32] {
    let digest = Sha256::digest(b"trust-buildcache/integrity/v2\0non-secret-cross-tool-key");
    let mut key = [0u8; 32];
    key.copy_from_slice(&digest);
    key
}

/// Compute the HMAC over a stored entry's artifacts + metadata.
///
/// Order is fixed (it's part of the seal). Any change to the order or to
/// the set of files hashed MUST be accompanied by a cache-key version
/// bump so old entries don't try to validate against the new composition.
pub(crate) fn compute_entry_hmac(dir: &Path) -> Result<String> {
    let key = compatibility_key();
    let mut mac = HmacSha256::new_from_slice(&key).expect("HMAC-SHA256 accepts any key length");
    update_entry_hmac(&mut mac, dir)?;
    Ok(format!("{:x}", mac.finalize().into_bytes()))
}

/// Write the HMAC sidecar file for an entry.
pub(crate) fn seal_entry(dir: &Path) -> Result<()> {
    let tag = compute_entry_hmac(dir)?;
    let path = dir.join(HMAC_FILENAME);
    std::fs::write(&path, tag).map_err(|e| BuildCacheError::io(&path, e))?;
    Ok(())
}

/// Verify the HMAC sidecar matches the current artifact bytes.
///
/// Returns `Ok(true)` only when the tag is present AND verifies. A missing
/// sidecar or any I/O failure returns `Ok(false)` -- the entry is treated
/// as corrupt by the caller, never as "trusted by default."
pub(crate) fn verify_entry(dir: &Path) -> Result<bool> {
    let path = dir.join(HMAC_FILENAME);
    let expected = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(_) => return Ok(false),
    };
    let expected = match decode_hmac(expected.trim()) {
        Some(expected) => expected,
        None => return Ok(false),
    };
    let key = compatibility_key();
    let mut mac = HmacSha256::new_from_slice(&key).expect("HMAC-SHA256 accepts any key length");
    match update_entry_hmac(&mut mac, dir) {
        Ok(()) => {}
        Err(_) => return Ok(false),
    }
    Ok(mac.verify_slice(&expected).is_ok())
}

/// Feed the exact framed byte sequence into the HMAC without materializing all
/// cached artifacts in memory.
///
/// File ordering and length framing are part of the seal. Length framing
/// (8-byte LE length prefix per file) prevents collisions where moving
/// bytes between adjacent files would produce the same concatenation.
fn update_entry_hmac(mac: &mut HmacSha256, dir: &Path) -> Result<()> {
    let mut buffer = [0u8; 64 * 1024];
    for name in SEALED_FILES {
        let path = dir.join(name);
        // Missing or unreadable inputs are errors, never an empty byte string:
        // an empty artifact and a failed read must not share a seal input.
        let path_metadata =
            std::fs::symlink_metadata(&path).map_err(|error| BuildCacheError::io(&path, error))?;
        if !path_metadata.file_type().is_file() {
            return Err(BuildCacheError::io(
                &path,
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    "sealed cache input is not a regular file",
                ),
            ));
        }
        let mut file =
            std::fs::File::open(&path).map_err(|error| BuildCacheError::io(&path, error))?;
        let length = file.metadata().map_err(|error| BuildCacheError::io(&path, error))?.len();
        mac.update(name.as_bytes());
        mac.update(&[0]);
        mac.update(&length.to_le_bytes());

        let mut remaining = length;
        while remaining != 0 {
            let limit = usize::try_from(remaining.min(buffer.len() as u64)).unwrap();
            let read = file
                .read(&mut buffer[..limit])
                .map_err(|error| BuildCacheError::io(&path, error))?;
            if read == 0 {
                return Err(BuildCacheError::io(
                    &path,
                    std::io::Error::new(
                        std::io::ErrorKind::UnexpectedEof,
                        "sealed cache input changed while it was being read",
                    ),
                ));
            }
            mac.update(&buffer[..read]);
            remaining -= read as u64;
        }
    }
    Ok(())
}

fn decode_hmac(hex: &str) -> Option<[u8; 32]> {
    if hex.len() != 64 {
        return None;
    }
    let mut decoded = [0u8; 32];
    for (index, chunk) in hex.as_bytes().chunks_exact(2).enumerate() {
        decoded[index] = (hex_nibble(chunk[0])? << 4) | hex_nibble(chunk[1])?;
    }
    Some(decoded)
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use tempfile::TempDir;

    use super::*;

    fn write_entry(dir: &Path) {
        std::fs::create_dir_all(dir).unwrap();
        for (name, body) in [
            ("rlib", b"rlib-bytes".as_ref()),
            ("rmeta", b"rmeta-bytes"),
            ("depfile", b"depfile"),
            ("certificate.json", b"{\"ok\":true}"),
            ("metadata.json", b"{\"key_hex\":\"\"}"),
        ] {
            let mut f = std::fs::File::create(dir.join(name)).unwrap();
            f.write_all(body).unwrap();
        }
    }

    #[test]
    fn seal_then_verify_succeeds() {
        let tmp = TempDir::new().unwrap();
        let dir = tmp.path().join("entry");
        write_entry(&dir);
        seal_entry(&dir).unwrap();
        assert!(verify_entry(&dir).unwrap());
    }

    #[test]
    fn compatibility_key_is_stable_and_nonzero() {
        assert_eq!(compatibility_key(), compatibility_key());
        assert_ne!(compatibility_key(), [0; 32]);
    }

    #[test]
    fn tampered_artifact_fails_verification() {
        let tmp = TempDir::new().unwrap();
        let dir = tmp.path().join("entry");
        write_entry(&dir);
        seal_entry(&dir).unwrap();
        // Tamper with the rlib.
        std::fs::write(dir.join("rlib"), b"different-rlib").unwrap();
        assert!(!verify_entry(&dir).unwrap());
    }

    #[test]
    fn missing_seal_returns_false() {
        let tmp = TempDir::new().unwrap();
        let dir = tmp.path().join("entry");
        write_entry(&dir);
        // No seal_entry call.
        assert!(!verify_entry(&dir).unwrap());
    }

    #[test]
    fn deleted_file_invalidates_seal() {
        let tmp = TempDir::new().unwrap();
        let dir = tmp.path().join("entry");
        write_entry(&dir);
        seal_entry(&dir).unwrap();
        // Delete an artifact post-seal.
        std::fs::remove_file(dir.join("certificate.json")).unwrap();
        assert!(!verify_entry(&dir).unwrap());
    }

    #[test]
    fn seal_refuses_missing_artifact_instead_of_hashing_an_empty_slot() {
        let tmp = TempDir::new().unwrap();
        let dir = tmp.path().join("entry");
        write_entry(&dir);
        std::fs::remove_file(dir.join("certificate.json")).unwrap();

        assert!(seal_entry(&dir).is_err());
        assert!(!dir.join(HMAC_FILENAME).exists());
    }
}
