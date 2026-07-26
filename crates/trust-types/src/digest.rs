//! Canonical digest and canonical-JSON primitives.
//!
//! A digest is an identity claim, not a convenience: caches key on it, evidence
//! rows are matched by it, and two subsystems that disagree about the bytes of
//! "the same" object silently disagree about whether a proof applies. Every
//! digest a Trust artifact carries therefore has to come from one
//! implementation, so a change to the algorithm is a change every reader sees
//! at once.
//!
//! ## Why canonical JSON lives beside the hash
//!
//! Serde emits struct fields in declaration order; `serde_json::Value` stores
//! objects in an order that depends on a *feature*. Without `preserve_order`,
//! `Value::Object` is a `BTreeMap` and re-serializes key-sorted; with it, an
//! `IndexMap` that re-serializes in insertion order. Cargo unifies features
//! across a workspace, so the same `T -> Value -> to_vec` code produces
//! different bytes depending on which workspace built it — and this repo really
//! does build the same crates both ways: the root workspace pulls
//! `serde_json/preserve_order` in through `first-party/trust-mc`'s driver,
//! while `crates/Cargo.toml` does not enable it anywhere.
//!
//! Digest material must therefore never be serialized straight out of a
//! `Value`. [`canonicalize_json_in_place`] rebuilds every object in key order,
//! which pins one byte sequence under both backings; the tests below pin that
//! the two backings agree by construction rather than by luck.
//!
//! Digest material that must survive out-of-JSON-range `i128`/`u128` first goes
//! through [`crate::json_digest::canonical_digest_json_value`]; this module
//! takes it from `Value` to bytes to hex.

use serde::Serialize;
use serde_json::Value;
use sha2::{Digest, Sha256};

/// Lowercase hex rendering of arbitrary bytes.
///
/// Hand-rolled rather than `format!("{:02x}")` per byte so the encoding is
/// locale- and formatter-independent and allocates exactly once.
#[must_use]
pub fn lowercase_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        encoded.push(HEX[usize::from(byte >> 4)] as char);
        encoded.push(HEX[usize::from(byte & 0x0f)] as char);
    }
    encoded
}

/// Lowercase SHA-256 hex over stable byte material.
#[must_use]
pub fn stable_sha256_hex(bytes: &[u8]) -> String {
    lowercase_hex(&Sha256::digest(bytes))
}

/// Lowercase SHA-256 hex over concatenated byte material.
///
/// Concatenation alone is not injective across part boundaries, so callers that
/// hash several fields must either fix every part's length or carry their own
/// separator — this helper does not invent one, because inventing one would
/// change the identity of everything that already hashes a fixed-width part
/// sequence.
#[must_use]
pub fn stable_sha256_hex_parts(parts: &[&[u8]]) -> String {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update(part);
    }
    lowercase_hex(&hasher.finalize())
}

/// Lowercase SHA-256 hex over everything `reader` yields.
///
/// Streaming rather than `read_to_end` so hashing a multi-gigabyte artifact
/// costs a fixed buffer — the release-evidence tools hash their own binaries,
/// and one of them already had to give up and report `[unreadable]`.
pub fn stable_sha256_hex_reader(mut reader: impl std::io::Read) -> std::io::Result<String> {
    let mut hasher = Sha256::new();
    let mut buffer = [0_u8; 8192];
    loop {
        let read = reader.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(lowercase_hex(&hasher.finalize()))
}

/// True iff `value` is exactly the 64-character lowercase hex form this module
/// produces.
///
/// Digest fields arriving over a wire are strings; accepting an uppercase,
/// truncated, or `sha256:`-prefixed spelling would let two spellings of one
/// digest compare unequal, so the check is exact.
#[must_use]
pub fn is_stable_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// Rewrite every JSON object in `value` into key order, in place.
///
/// This is what makes a `Value`-derived digest independent of the
/// `serde_json/preserve_order` feature (see the module header). Both `Map`
/// backings re-serialize in the order this leaves behind: `BTreeMap` because it
/// is sorted, `IndexMap` because insertion happened in sorted order.
pub fn canonicalize_json_in_place(value: &mut Value) {
    match value {
        Value::Array(values) => {
            for value in values {
                canonicalize_json_in_place(value);
            }
        }
        Value::Object(object) => {
            let mut entries = std::mem::take(object).into_iter().collect::<Vec<_>>();
            entries.sort_by(|left, right| left.0.cmp(&right.0));
            for (key, mut value) in entries {
                canonicalize_json_in_place(&mut value);
                object.insert(key, value);
            }
        }
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => {}
    }
}

/// Key-ordered copy of `value`.
#[must_use]
pub fn canonical_json_value(value: &Value) -> Value {
    let mut canonical = value.clone();
    canonicalize_json_in_place(&mut canonical);
    canonical
}

/// Canonical JSON bytes for any serializable digest material.
///
/// Goes through `Value` deliberately: the point is to reach the key-ordering
/// step, which a direct `to_vec` skips.
pub fn canonical_json_bytes<T>(value: &T) -> Result<Vec<u8>, serde_json::Error>
where
    T: ?Sized + Serialize,
{
    let mut value = serde_json::to_value(value)?;
    canonicalize_json_in_place(&mut value);
    serde_json::to_vec(&value)
}

/// Lowercase SHA-256 hex over [`canonical_json_bytes`].
pub fn canonical_json_sha256<T>(value: &T) -> Result<String, serde_json::Error>
where
    T: ?Sized + Serialize,
{
    canonical_json_bytes(value).map(|bytes| stable_sha256_hex(&bytes))
}

/// True iff `bytes` is already exactly its own canonical JSON encoding.
///
/// Envelope validators use this to refuse a payload whose digest was taken over
/// a different spelling of the same value — the check every hand-rolled
/// re-serialization comparison in this repo was performing separately.
#[must_use]
pub fn is_canonical_json(bytes: &[u8]) -> bool {
    let Ok(mut value) = serde_json::from_slice::<Value>(bytes) else {
        return false;
    };
    canonicalize_json_in_place(&mut value);
    serde_json::to_vec(&value).is_ok_and(|canonical| canonical == bytes)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn hex_and_sha256_pin_their_bytes() {
        assert_eq!(lowercase_hex(&[0x00, 0x0f, 0xa5, 0xff]), "000fa5ff");
        assert_eq!(lowercase_hex(&[]), "");
        // NIST SHA-256 of the empty string and of "abc"; if either of these
        // moves, every stored digest in the repo has changed meaning.
        assert_eq!(
            stable_sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        );
        assert_eq!(
            stable_sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        );
        // Parts hash exactly the concatenation — no injected separator, which
        // would silently rewrite the identity of every existing parts caller.
        assert_eq!(stable_sha256_hex_parts(&[b"a", b"bc"]), stable_sha256_hex(b"abc"));
        assert_eq!(stable_sha256_hex_parts(&[]), stable_sha256_hex(b""));
    }

    #[test]
    fn the_historical_hex_spellings_all_agree() {
        // Before this module there were several hand-written spellings of
        // "sha256 then lowercase hex" scattered across the crates, and every
        // stored digest in the repo was produced by one of them. Consolidating
        // is only safe because they agree bit for bit; this pins that, so a
        // future rewrite of `lowercase_hex` cannot silently re-key the caches
        // and stored evidence that those spellings produced.
        for material in [b"".as_slice(), b"abc", b"\x00\xff\x7f\x80", &[0x5a; 1000]] {
            let digest = Sha256::digest(material);
            let canonical = stable_sha256_hex(material);
            assert_eq!(canonical, format!("{digest:x}"));
            assert_eq!(
                canonical,
                digest.iter().map(|byte| format!("{byte:02x}")).collect::<String>()
            );
            assert_eq!(canonical.len(), 64);
            assert!(is_stable_sha256_hex(&canonical));
        }
    }

    #[test]
    fn streaming_agrees_with_the_in_memory_digest() {
        // The buffered reader must not be a second algorithm: a release gate
        // that streams a binary and a report that hashed it in memory have to
        // land on one identity. Sized to cross the 8 KiB buffer boundary.
        let material: Vec<u8> = (0..20_000_u32).map(|index| (index % 251) as u8).collect();
        assert_eq!(
            stable_sha256_hex_reader(material.as_slice()).unwrap(),
            stable_sha256_hex(&material),
        );
        assert_eq!(stable_sha256_hex_reader(&[][..]).unwrap(), stable_sha256_hex(b""));
    }

    #[test]
    fn only_the_exact_lowercase_form_validates() {
        let digest = stable_sha256_hex(b"abc");
        assert!(is_stable_sha256_hex(&digest));
        assert!(!is_stable_sha256_hex(&digest.to_uppercase()));
        assert!(!is_stable_sha256_hex(&digest[..63]));
        assert!(!is_stable_sha256_hex(&format!("sha256:{digest}")));
        assert!(!is_stable_sha256_hex(&"g".repeat(64)));
    }

    #[test]
    fn canonical_json_is_independent_of_the_map_backing() {
        // The `preserve_order` hazard, exercised: build the same object with
        // keys inserted in the WORST order for each backing and require one
        // byte sequence out. Under `BTreeMap` the insertion order is discarded;
        // under `IndexMap` it is not — canonicalization is what makes the two
        // agree, and this assertion fails the moment a caller drops it.
        let mut descending = serde_json::Map::new();
        descending.insert("zulu".to_string(), json!(1));
        descending.insert("mike".to_string(), json!({"y": 1, "x": 2}));
        descending.insert("alpha".to_string(), json!([{"b": 1, "a": 2}]));
        let mut ascending = serde_json::Map::new();
        ascending.insert("alpha".to_string(), json!([{"a": 2, "b": 1}]));
        ascending.insert("mike".to_string(), json!({"x": 2, "y": 1}));
        ascending.insert("zulu".to_string(), json!(1));

        let descending = canonical_json_value(&Value::Object(descending));
        let ascending = canonical_json_value(&Value::Object(ascending));
        assert_eq!(
            serde_json::to_vec(&descending).unwrap(),
            serde_json::to_vec(&ascending).unwrap()
        );
        assert_eq!(
            serde_json::to_string(&descending).unwrap(),
            r#"{"alpha":[{"a":2,"b":1}],"mike":{"x":2,"y":1},"zulu":1}"#,
        );
    }

    #[test]
    fn canonical_bytes_reorder_declaration_order_fields() {
        // A derived struct serializes in DECLARATION order; canonical bytes must
        // not. This is the case that silently forks a digest between a root-
        // workspace build and a `crates/` build when a caller skips
        // canonicalization.
        #[derive(Serialize)]
        struct Span {
            file: &'static str,
            line_start: u32,
            col_start: u32,
        }
        let span = Span { file: "demo.rs", line_start: 3, col_start: 1 };
        assert_eq!(
            String::from_utf8(canonical_json_bytes(&span).unwrap()).unwrap(),
            r#"{"col_start":1,"file":"demo.rs","line_start":3}"#,
        );
        assert_ne!(serde_json::to_vec(&span).unwrap(), canonical_json_bytes(&span).unwrap());
        assert_eq!(
            canonical_json_sha256(&span).unwrap(),
            stable_sha256_hex(&canonical_json_bytes(&span).unwrap()),
        );
    }

    #[test]
    fn only_canonical_bytes_validate_as_canonical() {
        let canonical = br#"{"a":1,"b":{"c":2,"d":3}}"#;
        assert!(is_canonical_json(canonical));
        // Same value, wrong key order.
        assert!(!is_canonical_json(br#"{"b":{"c":2,"d":3},"a":1}"#));
        // Same value, pretty-printed.
        assert!(!is_canonical_json(b"{\n  \"a\": 1,\n  \"b\": {\"c\": 2, \"d\": 3}\n}"));
        assert!(!is_canonical_json(b"not json"));
    }
}
