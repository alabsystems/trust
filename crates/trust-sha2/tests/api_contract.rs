// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **Every measured consumption form, compiled and executed.**
//!
//! The API contract for this crate was extracted from the ~130 real call sites
//! under `crates/`, `targo-trust/`, `src/tools/` and `compiler/`. Thirteen
//! distinct ways of consuming a digest and six distinct `update` argument
//! shapes were found. Each appears below exactly as it appears at the site it
//! is named after.
//!
//! This file exists because the swap fails at COMPILE time or not at all: an
//! `AsRef` where a `Deref` was needed, or a `&[u8]` parameter where a by-value
//! `[u8; 8]` is passed, is not a subtle behaviour difference — it is ~130 build
//! errors in twenty crates, discovered during integration instead of here.
//!
//! Keeping it as a test rather than a doc example means it also *runs*, so the
//! forms are checked for agreement with each other, not only for typechecking.

use trust_sha2::{Digest, Digest32, Sha256};

const EXPECTED_HELLO: &str = "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9";

// ---------------------------------------------------------------------------
// `update` argument shapes (contract §1c). All six must typecheck.
// ---------------------------------------------------------------------------

#[test]
fn update_accepts_every_measured_argument_shape() {
    let mut hasher = Sha256::new();

    // [u8; 8] BY VALUE — trust-buildcache/src/key.rs:95, trust-cache/src/mir_hash.rs:81
    // (both at 3a1cb55f071; T11 deleted them).
    // This is the shape that forces `impl AsRef<[u8]>`; a `&[u8]` parameter
    // would reject it and it appears at ~20 sites.
    hasher.update(7u64.to_le_bytes());

    // [u8; 1] BY VALUE — trust-router bit/nibble packing.
    let bit = true;
    hasher.update([u8::from(bit)]);
    hasher.update([(0x0a_u8 << 4) | 0x0b]);

    // &[u8; N] literal — the NUL field separator of the retired `trust-deps`
    // crate's digest (removed by TRUST-08, 2026-09-24).
    hasher.update(b"\0");

    // &[u8] slice — trust-types/src/digest.rs:87.
    let buffer = [1u8, 2, 3, 4, 5];
    hasher.update(&buffer[..3]);

    // &Vec<u8> — trust-cache/src/mir_hash.rs:84 (at 3a1cb55f071; T11 deleted it).
    let body_json: Vec<u8> = b"{}".to_vec();
    hasher.update(&body_json);

    // &&[u8] — trust-types/src/digest.rs:67, iterating `&[&[u8]]`.
    let parts: &[&[u8]] = &[b"a", b"b"];
    for part in parts {
        hasher.update(part);
    }

    // &str::as_bytes() — the most common shape of all.
    hasher.update("text".as_bytes());

    let _ = hasher.finalize();
}

// ---------------------------------------------------------------------------
// Digest output consumption forms 1-13 (contract §1d).
// ---------------------------------------------------------------------------

/// Forms 1, 2, 3: `format!("{:x}", ..)`, inline-arg `{hash:x}`, and prefixed.
#[test]
fn form_1_2_3_lower_hex() {
    let mut hasher = Sha256::new();
    hasher.update(b"hello world");
    assert_eq!(format!("{:x}", hasher.finalize()), EXPECTED_HELLO);

    let hash = Sha256::digest(b"hello world");
    assert_eq!(format!("{hash:x}"), EXPECTED_HELLO);

    let digest = Sha256::digest(b"hello world");
    assert_eq!(format!("sha256:{digest:x}"), format!("sha256:{EXPECTED_HELLO}"));
}

/// Form 4: `lowercase_hex(&Sha256::digest(bytes))` — deref COERCION into a
/// `&[u8]` parameter. `AsRef` does not provide this.
#[test]
fn form_4_deref_coercion_into_slice_parameter() {
    fn lowercase_hex(bytes: &[u8]) -> String {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let mut encoded = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            encoded.push(HEX[usize::from(byte >> 4)] as char);
            encoded.push(HEX[usize::from(byte & 0x0f)] as char);
        }
        encoded
    }

    assert_eq!(lowercase_hex(&Sha256::digest(b"hello world")), EXPECTED_HELLO);
}

/// Form 5: `key.copy_from_slice(&result)` — 20+ sites.
#[test]
fn form_5_copy_from_slice() {
    let mut hasher = Sha256::new();
    hasher.update(b"hello world");
    let result = hasher.finalize();
    let mut key = [0u8; 32];
    key.copy_from_slice(&result);
    assert_eq!(key[0], 0xb9);
    assert_eq!(key[31], 0xe9);
}

/// Form 6: passing `&digest` to a `&[u8]`-taking helper by name.
#[test]
fn form_6_named_helper_taking_slice() {
    fn lowercase_sha256(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
    let digest = Sha256::digest(b"hello world");
    assert_eq!(lowercase_sha256(&digest), EXPECTED_HELLO);
}

/// Form 7: integer index — `digest[0]`, `digest[1]`.
#[test]
fn form_7_integer_index() {
    let digest = Sha256::digest(b"hello world");
    assert_eq!(digest[0], 0xb9);
    assert_eq!(digest[1], 0x4d);
    assert_eq!(digest[31], 0xe9);
}

/// Form 8: range index then `try_into` — `digest[..8].try_into()`.
#[test]
fn form_8_range_index() {
    let digest = Sha256::digest(b"hello world");
    let prefix: [u8; 8] = digest[..8].try_into().expect("32-byte digest has 8 bytes");
    assert_eq!(prefix, [0xb9, 0x4d, 0x27, 0xb9, 0x93, 0x4d, 0x3e, 0x08]);
}

/// Form 9: `let computed: [u8; 32] = hasher.finalize().into();` — 11 sites.
#[test]
fn form_9_into_fixed_array() {
    let mut hasher = Sha256::new();
    hasher.update(b"hello world");
    let computed: [u8; 32] = hasher.finalize().into();
    assert_eq!(computed[0], 0xb9);

    // And the reverse direction, used when reconstructing a stored digest.
    let round_tripped: Digest32 = computed.into();
    assert_eq!(format!("{round_tripped:x}"), EXPECTED_HELLO);
}

/// Form 10: passed BY VALUE into an `impl AsRef<[u8]>` parameter, where no
/// deref coercion is available — `sha256_hex(digest.finalize())`.
#[test]
fn form_10_by_value_into_as_ref_parameter() {
    fn sha256_hex(digest: impl AsRef<[u8]>) -> String {
        let bytes = digest.as_ref();
        let mut value = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            use std::fmt::Write as _;
            write!(&mut value, "{byte:02x}").expect("String write cannot fail");
        }
        value
    }

    let mut hasher = Sha256::new();
    hasher.update(b"hello world");
    assert_eq!(sha256_hex(hasher.finalize()), EXPECTED_HELLO);
}

/// Form 11: `.as_slice()`.
#[test]
fn form_11_as_slice() {
    let digest = Sha256::digest(b"hello world");
    assert_eq!(digest.as_slice().len(), 32);
    assert_eq!(digest.as_slice()[0], 0xb9);
}

/// Form 12: `.iter().map(|b| format!("{b:02x}"))`.
#[test]
fn form_12_iter_over_reference() {
    let digest = Sha256::digest(b"hello world");
    let rendered: String = digest.iter().map(|b| format!("{b:02x}")).collect();
    assert_eq!(rendered, EXPECTED_HELLO);
}

/// Form 13: `for byte in digest { .. }` — by-value `IntoIterator<Item = u8>`.
#[test]
fn form_13_into_iterator_by_value() {
    let mut hasher = Sha256::new();
    hasher.update(b"hello world");
    let digest = hasher.finalize();

    let mut out = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write as _;
        let _ = write!(out, "{byte:02x}");
        // `byte` must be a `u8` VALUE, not a reference: arithmetic on it is
        // what pins the semantics at the site this form came from.
        let _high: usize = usize::from(byte >> 4);
    }
    assert_eq!(out, EXPECTED_HELLO);
}

// ---------------------------------------------------------------------------
// `Sha256` in TYPE position (contract §1e) — 3 sites, all `&mut Sha256`.
// ---------------------------------------------------------------------------

/// trust-report/src/json_output.rs:16 — a newtype over `&mut Sha256`
/// implementing `std::io::Write`.
#[test]
fn type_position_behind_mutable_reference() {
    struct DigestWriter<'a>(&'a mut Sha256);

    impl std::io::Write for DigestWriter<'_> {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            self.0.update(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    // `update_field` is the retired `trust-deps` crate's digest helper (removed
    // by TRUST-08, 2026-09-24); `hash_bytes` is trust-buildcache/src/key.rs:94
    // (removed by T11, 2026-10-16).
    fn update_field(digest: &mut Sha256, value: &str) {
        digest.update(value.as_bytes());
        digest.update(b"\0");
    }
    fn hash_bytes(hasher: &mut Sha256, label: &[u8], value: &[u8]) {
        hasher.update((label.len() as u64).to_le_bytes());
        hasher.update(label);
        hasher.update((value.len() as u64).to_le_bytes());
        hasher.update(value);
    }
    fn hash_count(hasher: &mut Sha256, label: &[u8], count: usize) {
        hash_bytes(hasher, label, &(count as u64).to_le_bytes());
    }

    let mut hasher = Sha256::new();
    {
        use std::io::Write as _;
        let mut writer = DigestWriter(&mut hasher);
        writer.write_all(b"hello ").expect("in-memory write cannot fail");
    }
    update_field(&mut hasher, "x");
    hash_bytes(&mut hasher, b"label", b"value");
    hash_count(&mut hasher, b"count", 3);
    let digest = hasher.finalize();

    // Recomputing the same byte stream one-shot must give the same digest —
    // otherwise the `&mut` threading is not equivalent to a single stream.
    let mut expected_stream: Vec<u8> = Vec::new();
    expected_stream.extend_from_slice(b"hello ");
    expected_stream.extend_from_slice(b"x");
    expected_stream.extend_from_slice(b"\0");
    expected_stream.extend_from_slice(&5u64.to_le_bytes());
    expected_stream.extend_from_slice(b"label");
    expected_stream.extend_from_slice(&5u64.to_le_bytes());
    expected_stream.extend_from_slice(b"value");
    expected_stream.extend_from_slice(&5u64.to_le_bytes());
    expected_stream.extend_from_slice(b"count");
    expected_stream.extend_from_slice(&8u64.to_le_bytes());
    expected_stream.extend_from_slice(&3u64.to_le_bytes());

    assert_eq!(format!("{digest:x}"), format!("{:x}", Sha256::digest(&expected_stream)));
}

/// The one-shot and incremental entry points must agree — 36 sites use
/// `Sha256::digest`, 168 use `new`/`update`/`finalize`, and nothing in the tree
/// would notice if they diverged.
#[test]
fn one_shot_and_incremental_agree() {
    for length in [0usize, 1, 55, 56, 63, 64, 128, 300] {
        let data: Vec<u8> = (0..length).map(|i| (i as u8).wrapping_mul(17)).collect();
        let mut hasher = Sha256::new();
        hasher.update(&data);
        assert_eq!(format!("{:x}", hasher.finalize()), format!("{:x}", Sha256::digest(&data)));
    }
}
