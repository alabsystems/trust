// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The two consumers' complete surface, compiled and executed.**
//!
//! `crates/trust-cache/src/integrity.rs` and
//! `crates/trust-buildcache/src/integrity.rs` are the only `hmac` consumers in
//! the tree. Their entire use of the crate is six forms, all reproduced below
//! verbatim in shape. Nothing else in `hmac`'s API is touched — no `Mac::new`,
//! no `generate_key`, `chain_update`, `finalize_reset`, `reset`, `verify`,
//! `verify_reset`, or `verify_truncated_left/right` — so this crate implements
//! none of them.
//!
//! The bodies here are transcriptions of the real functions, so that a
//! signature change that would break integration breaks this test first.

use trust_hmac::{Hmac, InvalidLength, Mac, MacError};
use trust_sha2::{Digest as _, Sha256};

/// Both consumers declare exactly this alias — so `Hmac` must be GENERIC over
/// the hash, not a SHA-256-specific type.
type HmacSha256 = Hmac<Sha256>;

// ---------------------------------------------------------------------------
// trust-cache/src/integrity.rs
// ---------------------------------------------------------------------------

/// `trust_cache::integrity::compute_cache_key`, transcribed.
fn compute_cache_key() -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update("exe-hash".as_bytes());
    hasher.update(b"\x00");
    hasher.update("hostname".as_bytes());
    let result = hasher.finalize();
    let mut key = [0u8; 32];
    key.copy_from_slice(&result);
    key
}

/// `trust_cache::integrity::compute_hmac`, transcribed.
fn compute_hmac(key: &[u8; 32], data: &[u8]) -> String {
    let mut mac = HmacSha256::new_from_slice(key).expect("HMAC-SHA256 accepts any key length");
    mac.update(data);
    let result = mac.finalize();
    format!("{:x}", result.into_bytes())
}

/// `trust_cache::integrity::verify_hmac`, transcribed.
fn verify_hmac(key: &[u8; 32], data: &[u8], expected_hex: &str) -> bool {
    if expected_hex.len() != 64 {
        return false;
    }
    let mut mac = HmacSha256::new_from_slice(key).expect("HMAC-SHA256 accepts any key length");
    mac.update(data);
    let expected_bytes = match hex_decode(expected_hex) {
        Some(bytes) => bytes,
        None => return false,
    };
    mac.verify_slice(&expected_bytes).is_ok()
}

fn hex_decode(text: &str) -> Option<Vec<u8>> {
    if text.len() % 2 != 0 {
        return None;
    }
    (0..text.len() / 2).map(|i| u8::from_str_radix(text.get(i * 2..i * 2 + 2)?, 16).ok()).collect()
}

// ---------------------------------------------------------------------------
// trust-buildcache/src/integrity.rs
// ---------------------------------------------------------------------------

/// `trust_buildcache::integrity::compatibility_key`, transcribed. Note it uses
/// the one-shot `Sha256::digest` and then `copy_from_slice(&digest)`, i.e. the
/// `Deref<Target = [u8]>` impl on the digest output.
fn compatibility_key() -> [u8; 32] {
    let digest = Sha256::digest(b"trust-buildcache/integrity/v2\0non-secret-cross-tool-key");
    let mut key = [0u8; 32];
    key.copy_from_slice(&digest);
    key
}

/// `trust_buildcache::integrity::update_entry_hmac`, transcribed — this is the
/// site that requires `&mut HmacSha256` in TYPE position, and that feeds the
/// MAC `&[u8; 1]` and `&[u8; 8]` values which must coerce to `&[u8]`.
fn update_entry_hmac(mac: &mut HmacSha256, files: &[(&str, &[u8])]) {
    let mut buffer = [0u8; 64 * 1024];
    for (name, contents) in files {
        let length = contents.len() as u64;
        mac.update(name.as_bytes());
        mac.update(&[0]);
        mac.update(&length.to_le_bytes());

        let mut offset = 0usize;
        while offset < contents.len() {
            let limit = (contents.len() - offset).min(buffer.len());
            buffer[..limit].copy_from_slice(&contents[offset..offset + limit]);
            mac.update(&buffer[..limit]);
            offset += limit;
        }
    }
}

/// `trust_buildcache::integrity::compute_entry_hmac`, transcribed.
fn compute_entry_hmac(files: &[(&str, &[u8])]) -> String {
    let key = compatibility_key();
    let mut mac = HmacSha256::new_from_slice(&key).expect("HMAC-SHA256 accepts any key length");
    update_entry_hmac(&mut mac, files);
    format!("{:x}", mac.finalize().into_bytes())
}

/// `trust_buildcache::integrity::verify_entry`, transcribed.
fn verify_entry(files: &[(&str, &[u8])], expected: &[u8]) -> bool {
    let key = compatibility_key();
    let mut mac = HmacSha256::new_from_slice(&key).expect("HMAC-SHA256 accepts any key length");
    update_entry_hmac(&mut mac, files);
    mac.verify_slice(expected).is_ok()
}

// ---------------------------------------------------------------------------
// The tests.
// ---------------------------------------------------------------------------

#[test]
fn trust_cache_surface_round_trips() {
    let key = compute_cache_key();
    let data = b"{\"entries\":[{\"key\":\"abc\"}]}";

    let tag = compute_hmac(&key, data);
    assert_eq!(tag.len(), 64, "an HMAC-SHA256 tag renders as 64 hex characters");
    assert!(tag.chars().all(|c| c.is_ascii_digit() || ('a'..='f').contains(&c)));

    assert!(verify_hmac(&key, data, &tag));
    assert!(!verify_hmac(&key, b"different data", &tag));
    assert!(!verify_hmac(&[0u8; 32], data, &tag), "a different key must not verify");
    assert!(!verify_hmac(&key, data, "not hex at all, and the wrong length entirely"));

    // The length pre-check in the real function short-circuits before decoding.
    assert!(!verify_hmac(&key, data, &tag[..63]));
}

#[test]
fn trust_buildcache_surface_round_trips() {
    let files: &[(&str, &[u8])] = &[
        ("rlib", &[0xab; 70_000]),
        ("rmeta", &[0xcd; 130]),
        ("depfile", b""),
        ("certificate.json", b"{\"verdict\":\"Proved\"}"),
        ("metadata.json", &[0x11; 65_536]),
    ];

    let tag = compute_entry_hmac(files);
    let decoded = hex_decode(&tag).expect("compute_entry_hmac emits hex");
    assert_eq!(decoded.len(), 32);
    assert!(verify_entry(files, &decoded));

    // Framing must actually distinguish: moving a byte across a file boundary
    // is the collision the length prefixes exist to prevent, and the seal must
    // change when it happens.
    let shifted: &[(&str, &[u8])] = &[
        ("rlib", &[0xab; 70_001]),
        ("rmeta", &[0xcd; 129]),
        ("depfile", b""),
        ("certificate.json", b"{\"verdict\":\"Proved\"}"),
        ("metadata.json", &[0x11; 65_536]),
    ];
    assert_ne!(compute_entry_hmac(shifted), tag);
    assert!(!verify_entry(shifted, &decoded));
}

/// `new_from_slice` returns a `Result` whose error is `Debug` — both call sites
/// `.expect(..)` it, which will not compile otherwise.
#[test]
fn new_from_slice_error_is_debug_and_never_occurs() {
    for key_length in [0usize, 1, 31, 32, 63, 64, 65, 200] {
        let key = vec![0x42u8; key_length];
        let result: Result<HmacSha256, InvalidLength> = HmacSha256::new_from_slice(&key);
        assert!(result.is_ok(), "HMAC accepts any key length; {key_length} was rejected");
        // Exercise the `.expect(..)` path itself, which needs `E: Debug`.
        let _ = HmacSha256::new_from_slice(&key).expect("HMAC-SHA256 accepts any key length");
    }

    // Both error types must be Debug/Display so a caller can report them.
    assert_eq!(format!("{:?}", InvalidLength), "InvalidLength");
    assert_eq!(format!("{InvalidLength}"), "invalid key length");
    assert_eq!(format!("{:?}", MacError), "MacError");
    assert_eq!(format!("{MacError}"), "MAC tag mismatch");
}

/// `finalize` and `verify_slice` take `self` BY VALUE: the MAC is consumed.
///
/// This is a compile-shape assertion as much as a behaviour one — if either
/// took `&mut self`, the transcriptions above would still compile but a
/// finalized MAC could be reused, which is a correctness trap.
#[test]
fn finalize_and_verify_consume_the_mac() {
    let key = [0x5au8; 32];

    let mut mac = HmacSha256::new_from_slice(&key).expect("any key length");
    mac.update(b"payload");
    let tag = mac.finalize().into_bytes();
    // `mac` is moved here; a second use would not compile.

    let mut verifier = HmacSha256::new_from_slice(&key).expect("any key length");
    verifier.update(b"payload");
    let outcome: Result<(), MacError> = verifier.verify_slice(&tag);
    assert!(outcome.is_ok());
}

/// The tag type is the hash's output type, so `LowerHex` lives on it — the
/// wrapper itself deliberately has none, matching the incumbent, because both
/// call sites write `format!("{:x}", result.into_bytes())`.
#[test]
fn tag_renders_as_lower_hex_after_into_bytes() {
    let mut mac = HmacSha256::new_from_slice(&[0x0bu8; 20]).expect("any key length");
    mac.update(b"Hi There");
    let bytes = mac.finalize().into_bytes();

    assert_eq!(
        format!("{bytes:x}"),
        "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
    );
    // And the digest-output forms the hash crate guarantees are still present.
    assert_eq!(bytes.len(), 32);
    assert_eq!(bytes[0], 0xb0);
    let raw: [u8; 32] = bytes.into();
    assert_eq!(raw[31], 0xf7);
}
