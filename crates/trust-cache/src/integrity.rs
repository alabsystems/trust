// trust-cache/src/integrity.rs: HMAC-SHA256 compatibility tags for cache files
//
// Computes HMAC-SHA256 over serialized cache entries using a key derived from
// the Trust executable hash and machine hostname. This detects accidental
// corruption and records copied from an incompatible producer. It does NOT
// authenticate against a writer with filesystem access: all derivation
// material is available locally, so that writer can recompute a valid tag.
//
// Never use this tag alone to authorize proof replay.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::OnceLock;

use hmac::{Hmac, Mac};
use sha2::{Digest, Sha256};

type HmacSha256 = Hmac<Sha256>;

static CACHE_COMPATIBILITY_KEY: OnceLock<[u8; 32]> = OnceLock::new();

/// Derive deterministic HMAC material from the current executable and host.
///
/// The value is SHA-256(executable_hash || hostname), providing machine-local
/// compatibility binding: a cache copied from another host/binary usually gets
/// rejected. It is **not secret**. Any local writer can derive it and forge a
/// valid tag, so callers must not treat successful verification as proof
/// authentication.
///
/// Exposed `pub` so sibling cache crates (e.g., `trust-buildcache`) can seal
/// their entries with the same machine-local compatibility binding.
#[must_use]
pub fn derive_cache_key() -> [u8; 32] {
    *CACHE_COMPATIBILITY_KEY.get_or_init(compute_cache_key)
}

fn compute_cache_key() -> [u8; 32] {
    let exe_hash = executable_hash();
    let hostname = machine_hostname();

    let mut hasher = Sha256::new();
    hasher.update(exe_hash.as_bytes());
    hasher.update(b"\x00");
    hasher.update(hostname.as_bytes());
    let result = hasher.finalize();
    let mut key = [0u8; 32];
    key.copy_from_slice(&result);
    key
}

/// Compute HMAC-SHA256 over the given data using the provided key.
///
/// Returns a hex-encoded HMAC tag (64 characters).
///
/// Exposed `pub` so sibling cache crates can use the same primitive.
#[must_use]
pub fn compute_hmac(key: &[u8; 32], data: &[u8]) -> String {
    let mut mac = HmacSha256::new_from_slice(key).expect("HMAC-SHA256 accepts any key length");
    mac.update(data);
    let result = mac.finalize();
    format!("{:x}", result.into_bytes())
}

/// Verify an HMAC-SHA256 compatibility tag over the given data.
///
/// Returns `true` if the tag matches, `false` if corrupted or from a different
/// binding. A match does not establish an adversarial writer did not forge it.
/// Uses constant-time comparison to prevent timing attacks.
///
/// Exposed `pub` so sibling cache crates can use the same primitive.
pub fn verify_hmac(key: &[u8; 32], data: &[u8], expected_hex: &str) -> bool {
    // HMAC-SHA256 is exactly 32 bytes / 64 hexadecimal characters. Reject an
    // impossible tag before decoding so an attacker-controlled cache field
    // cannot turn a constant-size comparison into input-sized allocation and
    // CPU work.
    if expected_hex.len() != 64 {
        return false;
    }
    let mut mac = HmacSha256::new_from_slice(key).expect("HMAC-SHA256 accepts any key length");
    mac.update(data);

    // Decode the expected hex tag
    let expected_bytes = match hex_decode(expected_hex) {
        Some(b) => b,
        None => return false,
    };

    // hmac::Mac::verify_slice uses constant-time comparison
    mac.verify_slice(&expected_bytes).is_ok()
}

/// SHA-256 hash of the current executable binary, hex-encoded.
///
/// Falls back to the executable path hash if the binary cannot be read
/// (e.g., deleted after launch). This remains sufficient for a best-effort
/// compatibility tag; neither branch is an authentication secret.
fn executable_hash() -> String {
    let exe_path = std::env::current_exe().unwrap_or_default();
    match std::fs::read(&exe_path) {
        Ok(bytes) => {
            let mut hasher = Sha256::new();
            hasher.update(&bytes);
            format!("{:x}", hasher.finalize())
        }
        Err(_) => {
            // Fallback: hash the path itself. Lossiness is acceptable here
            // because this value is only a non-authoritative compatibility tag,
            // never a solver identity or proof-cache key.
            let mut hasher = Sha256::new();
            hasher.update(exe_path.to_string_lossy().as_bytes());
            format!("{:x}", hasher.finalize())
        }
    }
}

/// Machine hostname, or "unknown" if unavailable.
///
/// Uses `std::env::var("HOSTNAME")` with fallback to `gethostname()` via
/// `std::process::Command`. No external crate dependency.
fn machine_hostname() -> String {
    // Try HOSTNAME env var first (set on most Linux/macOS systems)
    if let Ok(h) = std::env::var("HOSTNAME")
        && !h.is_empty()
    {
        return h;
    }
    // Fallback: call `hostname` command
    std::process::Command::new("hostname")
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "unknown".to_string())
}

/// Decode a hex string to bytes. Returns `None` on invalid hex.
fn hex_decode(hex: &str) -> Option<Vec<u8>> {
    if !hex.len().is_multiple_of(2) {
        return None;
    }
    // Deliberately NOT `Vec::with_capacity(hex.len() / 2)`: an input-sized
    // pre-allocation is an unbounded allocation obligation (the hex string is
    // untrusted cache-file input). Amortized push growth is fine for the
    // 64-char HMAC tags this decodes in practice.
    let mut bytes = Vec::new();
    for chunk in hex.as_bytes().chunks(2) {
        let high = hex_nibble(chunk[0])?;
        // Fail closed on a short chunk. Unreachable: the even-length guard
        // above means chunks(2) only yields full pairs — but decoding must
        // never index past the chunk if that invariant were ever broken.
        let low = hex_nibble(*chunk.get(1)?)?;
        bytes.push((high << 4) | low);
    }
    Some(bytes)
}

/// Convert a single hex ASCII byte to its nibble value.
fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_derive_cache_key_deterministic() {
        let k1 = derive_cache_key();
        let k2 = derive_cache_key();
        assert_eq!(k1, k2, "key derivation must be deterministic");
    }

    #[test]
    fn test_derive_cache_key_nonzero() {
        let key = derive_cache_key();
        assert_ne!(key, [0u8; 32], "derived key must not be all zeros");
    }

    #[test]
    fn test_compute_hmac_deterministic() {
        let key = [0xABu8; 32];
        let data = b"cache entry data";
        let h1 = compute_hmac(&key, data);
        let h2 = compute_hmac(&key, data);
        assert_eq!(h1, h2, "HMAC must be deterministic");
    }

    #[test]
    fn test_compute_hmac_hex_length() {
        let key = [0x42u8; 32];
        let hmac = compute_hmac(&key, b"test");
        assert_eq!(hmac.len(), 64, "HMAC-SHA256 hex is 64 chars");
        assert!(hmac.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_verify_hmac_valid() {
        let key = [0x42u8; 32];
        let data = b"important cache data";
        let tag = compute_hmac(&key, data);
        assert!(verify_hmac(&key, data, &tag), "valid HMAC must verify");
    }

    #[test]
    fn test_verify_hmac_tampered_data() {
        let key = [0x42u8; 32];
        let data = b"original data";
        let tag = compute_hmac(&key, data);
        let tampered = b"tampered data";
        assert!(!verify_hmac(&key, tampered, &tag), "tampered data must fail verification");
    }

    #[test]
    fn test_verify_hmac_wrong_key() {
        let key1 = [0x42u8; 32];
        let key2 = [0x43u8; 32];
        let data = b"cache data";
        let tag = compute_hmac(&key1, data);
        assert!(!verify_hmac(&key2, data, &tag), "wrong key must fail verification");
    }

    #[test]
    fn test_verify_hmac_invalid_hex() {
        let key = [0x42u8; 32];
        let data = b"test";
        assert!(!verify_hmac(&key, data, "not-hex!"), "invalid hex must fail");
        assert!(!verify_hmac(&key, data, "abc"), "odd-length hex must fail");
        assert!(!verify_hmac(&key, data, &"z".repeat(64)), "invalid full tag must fail");
        assert!(
            !verify_hmac(&key, data, &"a".repeat(1024 * 1024)),
            "oversized tag must fail before input-sized decoding"
        );
    }

    #[test]
    fn test_verify_hmac_empty_tag() {
        let key = [0x42u8; 32];
        let data = b"test";
        assert!(!verify_hmac(&key, data, ""), "empty tag must fail verification");
    }

    #[test]
    fn test_different_data_different_hmac() {
        let key = [0x42u8; 32];
        let h1 = compute_hmac(&key, b"data1");
        let h2 = compute_hmac(&key, b"data2");
        assert_ne!(h1, h2, "different data must produce different HMACs");
    }

    #[test]
    fn test_hex_decode_roundtrip() {
        let key = [0x42u8; 32];
        let tag = compute_hmac(&key, b"test");
        let decoded = hex_decode(&tag);
        assert!(decoded.is_some());
        assert_eq!(decoded.unwrap().len(), 32, "SHA-256 HMAC is 32 bytes");
    }

    #[test]
    fn test_hex_decode_odd_length_fails_closed() {
        assert_eq!(hex_decode("a"), None, "1-char hex must fail closed");
        assert_eq!(hex_decode("abc"), None, "odd-length hex must fail closed");
        assert_eq!(
            hex_decode(&"f".repeat(65)),
            None,
            "odd-length tag-sized hex must fail closed"
        );
    }

    #[test]
    fn test_hex_decode_invalid_char_fails_closed() {
        assert_eq!(hex_decode("zz"), None, "non-hex chars must fail closed");
        assert_eq!(hex_decode("0g"), None, "invalid low nibble must fail closed");
        assert_eq!(hex_decode("g0"), None, "invalid high nibble must fail closed");
        assert_eq!(hex_decode("12 4"), None, "embedded space must fail closed");
        assert_eq!(hex_decode("ab\u{0000}d"), None, "NUL byte must fail closed");
    }

    #[test]
    fn test_hex_decode_valid_inputs() {
        assert_eq!(hex_decode(""), Some(vec![]), "empty hex decodes to empty bytes");
        assert_eq!(hex_decode("00"), Some(vec![0x00]));
        assert_eq!(hex_decode("ff"), Some(vec![0xff]));
        assert_eq!(hex_decode("FF"), Some(vec![0xff]), "uppercase accepted");
        assert_eq!(hex_decode("00ff10Ab"), Some(vec![0x00, 0xff, 0x10, 0xab]));
    }
}
