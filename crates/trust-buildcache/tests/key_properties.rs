//! Property-based tests for [`CacheKey`] composition.
//!
//! Contract:
//! 1. Determinism: same inputs -> same key (across random inputs).
//! 2. Sensitivity: any single field change moves the key (across random inputs).
//! 3. Output shape: hex is always 64 chars, lowercase.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;

use proptest::prelude::*;
use trust_buildcache::{CacheInputs, CacheKey};

#[derive(Debug)]
struct OwnedInputs {
    source_hashes: Vec<(PathBuf, [u8; 32])>,
    transitive_dep_hashes: Vec<CacheKey>,
    trustc_fingerprint: String,
    dmath_versions: Vec<(String, String)>,
    verification_policy: String,
    target_triple: String,
    profile: String,
    codegen_flags: Vec<String>,
    rustc_version: String,
    edition: String,
}

impl OwnedInputs {
    fn as_cache_inputs(&self) -> CacheInputs<'_> {
        CacheInputs {
            source_hashes: &self.source_hashes,
            transitive_dep_hashes: &self.transitive_dep_hashes,
            trustc_fingerprint: &self.trustc_fingerprint,
            dmath_versions: &self.dmath_versions,
            verification_policy: &self.verification_policy,
            target_triple: &self.target_triple,
            profile: &self.profile,
            codegen_flags: &self.codegen_flags,
            rustc_version: &self.rustc_version,
            edition: &self.edition,
        }
    }
}

fn arb_path() -> impl Strategy<Value = PathBuf> {
    "[a-zA-Z][a-zA-Z0-9_/.-]{0,32}".prop_map(PathBuf::from)
}

fn arb_hash() -> impl Strategy<Value = [u8; 32]> {
    any::<[u8; 32]>()
}

fn arb_source_hashes() -> impl Strategy<Value = Vec<(PathBuf, [u8; 32])>> {
    prop::collection::vec((arb_path(), arb_hash()), 0..4)
}

fn arb_string() -> impl Strategy<Value = String> {
    "[a-z0-9.]{0,16}".prop_map(String::from)
}

fn arb_inputs() -> impl Strategy<Value = OwnedInputs> {
    (
        arb_source_hashes(),
        prop::collection::vec(arb_hash(), 0..4),
        arb_string(),
        prop::collection::vec((arb_string(), arb_string()), 0..3),
        arb_string(),
        arb_string(),
        arb_string(),
        prop::collection::vec(arb_string(), 0..3),
        arb_string(),
        arb_string(),
    )
        .prop_map(
            |(
                source_hashes,
                dep_hashes_bytes,
                trustc,
                dmath,
                policy,
                triple,
                profile,
                flags,
                rustc,
                edition,
            )| {
                OwnedInputs {
                    source_hashes,
                    transitive_dep_hashes: dep_hashes_bytes
                        .into_iter()
                        .map(CacheKey::from_bytes)
                        .collect(),
                    trustc_fingerprint: trustc,
                    dmath_versions: dmath,
                    verification_policy: policy,
                    target_triple: triple,
                    profile,
                    codegen_flags: flags,
                    rustc_version: rustc,
                    edition,
                }
            },
        )
}

fn clone_inputs(other: &OwnedInputs) -> OwnedInputs {
    OwnedInputs {
        source_hashes: other.source_hashes.clone(),
        transitive_dep_hashes: other.transitive_dep_hashes.clone(),
        trustc_fingerprint: other.trustc_fingerprint.clone(),
        dmath_versions: other.dmath_versions.clone(),
        verification_policy: other.verification_policy.clone(),
        target_triple: other.target_triple.clone(),
        profile: other.profile.clone(),
        codegen_flags: other.codegen_flags.clone(),
        rustc_version: other.rustc_version.clone(),
        edition: other.edition.clone(),
    }
}

proptest! {
    /// Property 1: determinism. Same inputs -> same key.
    #[test]
    fn cache_key_is_deterministic_across_inputs(inputs in arb_inputs()) {
        let a = CacheKey::compute(&inputs.as_cache_inputs());
        let b = CacheKey::compute(&inputs.as_cache_inputs());
        prop_assert_eq!(a, b);
    }

    /// Property 2: changing the trustc fingerprint changes the key.
    #[test]
    fn cache_key_sensitive_to_trustc_fingerprint(
        inputs in arb_inputs(),
        suffix in "[a-z]{1,4}"
    ) {
        let original = CacheKey::compute(&inputs.as_cache_inputs());
        let mut perturbed = clone_inputs(&inputs);
        perturbed.trustc_fingerprint.push_str(&suffix);
        perturbed.trustc_fingerprint.push('!');
        let changed = CacheKey::compute(&perturbed.as_cache_inputs());
        prop_assert_ne!(original, changed);
    }

    /// Property 3: changing the verification policy changes the key.
    #[test]
    fn cache_key_sensitive_to_verification_policy(
        inputs in arb_inputs(),
        suffix in "[a-z]{1,4}"
    ) {
        let original = CacheKey::compute(&inputs.as_cache_inputs());
        let mut perturbed = clone_inputs(&inputs);
        perturbed.verification_policy.push_str(&suffix);
        perturbed.verification_policy.push('!');
        let changed = CacheKey::compute(&perturbed.as_cache_inputs());
        prop_assert_ne!(original, changed);
    }

    /// Property 4: appending a new dmath_version entry changes the key.
    #[test]
    fn cache_key_sensitive_to_dmath_versions(
        inputs in arb_inputs(),
        new_name in "[a-z]{2,6}",
        new_version in "[0-9.]{2,8}"
    ) {
        let original = CacheKey::compute(&inputs.as_cache_inputs());
        let mut perturbed = clone_inputs(&inputs);
        perturbed.dmath_versions.push((format!("{new_name}-unique"), new_version));
        let changed = CacheKey::compute(&perturbed.as_cache_inputs());
        prop_assert_ne!(original, changed);
    }

    /// Property 5: hex output is 64 chars, lowercase hex digits.
    #[test]
    fn hex_is_64_chars_lowercase_hex(inputs in arb_inputs()) {
        let key = CacheKey::compute(&inputs.as_cache_inputs());
        let hex = key.hex();
        prop_assert_eq!(hex.len(), 64);
        prop_assert!(hex.chars().all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase()));
    }
}
