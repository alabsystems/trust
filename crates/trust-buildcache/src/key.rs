//! Content-addressed cache keys.
//!
//! A [`CacheKey`] is a SHA-256 over the experimental input schema defined by
//! [`CacheInputs`]. It is not yet a complete Cargo/rustc build fingerprint.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt::Write as _;
use std::path::PathBuf;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Stable content-addressed identifier for one cached build entry.
///
/// This identifies entries within the experimental cache API. Production reuse
/// is intentionally unwired: the v2 schema does not yet cover every Cargo,
/// build-script, proc-macro, target, environment, and dependency input needed
/// to claim equivalent compiler output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CacheKey([u8; 32]);

impl CacheKey {
    /// Construct from raw bytes (e.g., when deserializing from cache state).
    #[must_use]
    pub fn from_bytes(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    /// Raw 32-byte digest.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Lowercase hex representation, 64 chars. Used for path components.
    #[must_use]
    pub fn hex(&self) -> String {
        let mut out = String::with_capacity(64);
        for b in &self.0 {
            let _ = write!(out, "{b:02x}");
        }
        out
    }

    /// Compute a cache key over the v2 experimental input subset.
    ///
    /// The hash composition is versioned by the leading domain-separation
    /// label (`trust-buildcache/v2`). Any change to the input set or framing
    /// must bump
    /// that label so prior cache entries are not matched against the new
    /// composition.
    #[must_use]
    pub fn compute(inputs: &CacheInputs<'_>) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(b"trust-buildcache/v2\0length-framed");

        hash_count(&mut hasher, b"source_hashes", inputs.source_hashes.len());
        for (path, hash) in inputs.source_hashes {
            hash_bytes(&mut hasher, b"source_path", path.as_os_str().as_encoded_bytes());
            hash_bytes(&mut hasher, b"source_hash", hash);
        }
        hash_count(&mut hasher, b"transitive_dep_hashes", inputs.transitive_dep_hashes.len());
        for dep in inputs.transitive_dep_hashes {
            hash_bytes(&mut hasher, b"transitive_dep_hash", dep.as_bytes());
        }
        hash_bytes(&mut hasher, b"trustc_fingerprint", inputs.trustc_fingerprint.as_bytes());
        hash_count(&mut hasher, b"dmath_versions", inputs.dmath_versions.len());
        for (name, version) in inputs.dmath_versions {
            hash_bytes(&mut hasher, b"dmath_name", name.as_bytes());
            hash_bytes(&mut hasher, b"dmath_version", version.as_bytes());
        }
        hash_bytes(&mut hasher, b"verification_policy", inputs.verification_policy.as_bytes());
        hash_bytes(&mut hasher, b"target_triple", inputs.target_triple.as_bytes());
        hash_bytes(&mut hasher, b"profile", inputs.profile.as_bytes());
        hash_count(&mut hasher, b"codegen_flags", inputs.codegen_flags.len());
        for flag in inputs.codegen_flags {
            hash_bytes(&mut hasher, b"codegen_flag", flag.as_bytes());
        }
        hash_bytes(&mut hasher, b"rustc_version", inputs.rustc_version.as_bytes());
        hash_bytes(&mut hasher, b"edition", inputs.edition.as_bytes());

        let digest = hasher.finalize();
        let mut bytes = [0u8; 32];
        bytes.copy_from_slice(&digest);
        Self(bytes)
    }
}

/// Feed one schema field with unambiguous length framing. Cache input strings
/// may contain newlines, `=`, or text that resembles the next field label; raw
/// delimiter concatenation would let distinct input tuples hash the same bytes.
fn hash_bytes(hasher: &mut Sha256, label: &[u8], value: &[u8]) {
    hasher.update((label.len() as u64).to_le_bytes());
    hasher.update(label);
    hasher.update((value.len() as u64).to_le_bytes());
    hasher.update(value);
}

fn hash_count(hasher: &mut Sha256, label: &[u8], count: usize) {
    hash_bytes(hasher, label, &(count as u64).to_le_bytes());
}

/// Inputs that determine a [`CacheKey`].
///
/// Experimental subset of inputs relevant to artifacts and verification.
/// Before a production consumer is added, this schema must be completed from
/// Cargo's resolved unit graph (including build-script/proc-macro outputs and
/// all tracked rustc inputs) and the domain-separation label in
/// [`CacheKey::compute`] must be bumped.
#[derive(Debug, Clone)]
pub struct CacheInputs<'a> {
    /// (path, SHA-256 of file content) for every source file fed to trustc,
    /// in deterministic order. Sort by path before passing.
    pub source_hashes: &'a [(PathBuf, [u8; 32])],

    /// Cache keys of every transitively-depended crate, in dep-graph order.
    pub transitive_dep_hashes: &'a [CacheKey],

    /// Stable fingerprint of the trustc binary that will perform the build.
    /// trust-router already exposes `solver_fingerprint`; the trustc-side
    /// equivalent is the binary content hash + the verification surface
    /// version.
    pub trustc_fingerprint: &'a str,

    /// (name, version) for every solver backend wired into this build:
    /// ay, trust-mc, trust-wp, trust-vc, ty, clean, ny.
    pub dmath_versions: &'a [(String, String)],

    /// Stable serialization of the verification policy in effect
    /// (proof level, per-VC timeout, abort-on-fail strictness, etc.).
    pub verification_policy: &'a str,

    pub target_triple: &'a str,
    pub profile: &'a str,
    pub codegen_flags: &'a [String],
    pub rustc_version: &'a str,
    pub edition: &'a str,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn empty_inputs<'a>() -> CacheInputs<'a> {
        CacheInputs {
            source_hashes: &[],
            transitive_dep_hashes: &[],
            trustc_fingerprint: "",
            dmath_versions: &[],
            verification_policy: "",
            target_triple: "",
            profile: "",
            codegen_flags: &[],
            rustc_version: "",
            edition: "",
        }
    }

    #[test]
    fn cache_key_is_deterministic() {
        let a = CacheKey::compute(&empty_inputs());
        let b = CacheKey::compute(&empty_inputs());
        assert_eq!(a, b);
    }

    #[test]
    fn cache_key_changes_with_trustc_fingerprint() {
        let mut inputs = empty_inputs();
        let a = CacheKey::compute(&inputs);
        inputs.trustc_fingerprint = "different";
        let b = CacheKey::compute(&inputs);
        assert_ne!(a, b);
    }

    #[test]
    fn cache_key_changes_with_dmath_versions() {
        let mut inputs = empty_inputs();
        let a = CacheKey::compute(&inputs);
        let versions = [("ay".to_string(), "1.2.3".to_string())];
        inputs.dmath_versions = &versions;
        let b = CacheKey::compute(&inputs);
        assert_ne!(a, b);
    }

    #[test]
    fn cache_key_changes_with_verification_policy() {
        let mut inputs = empty_inputs();
        let a = CacheKey::compute(&inputs);
        inputs.verification_policy = "L1+strict";
        let b = CacheKey::compute(&inputs);
        assert_ne!(a, b);
    }

    #[test]
    fn cache_key_length_framing_distinguishes_embedded_field_delimiters() {
        // The old newline-delimited encoding serialized both flag lists as the
        // exact bytes `flag:a\nflag:b\n`, aliasing distinct compiler inputs.
        let joined = ["a\nflag:b".to_string()];
        let split = ["a".to_string(), "b".to_string()];
        let mut inputs = empty_inputs();
        inputs.codegen_flags = &joined;
        let joined_key = CacheKey::compute(&inputs);
        inputs.codegen_flags = &split;
        let split_key = CacheKey::compute(&inputs);

        assert_ne!(joined_key, split_key);

        // Pair framing matters independently of list-element framing.
        let joined_pair = [("ay".to_string(), "1\ndmath:ty=2".to_string())];
        let split_pairs =
            [("ay".to_string(), "1".to_string()), ("ty".to_string(), "2".to_string())];
        inputs.codegen_flags = &[];
        inputs.dmath_versions = &joined_pair;
        let joined_pair_key = CacheKey::compute(&inputs);
        inputs.dmath_versions = &split_pairs;
        let split_pair_key = CacheKey::compute(&inputs);

        assert_ne!(joined_pair_key, split_pair_key);
    }

    #[test]
    fn hex_is_64_chars_lowercase() {
        let key = CacheKey::compute(&empty_inputs());
        let hex = key.hex();
        assert_eq!(hex.len(), 64);
        assert!(hex.chars().all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase()));
    }
}
