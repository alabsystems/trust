//! Integration tests for the cache's "no pure binary hits" + HMAC seal
//! invariants under realistic tampering scenarios.
//!
//! These tests exercise the full lifecycle (store → lookup → tamper →
//! lookup-miss → gc-evict) end-to-end against a real filesystem cache,
//! rather than each layer in isolation.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;

use tempfile::TempDir;
use trust_buildcache::{BuildCache, CacheInputs, CacheKey, StoreRequest};

fn key_for(label: &str) -> CacheKey {
    let policy = label.to_string();
    let inputs = CacheInputs {
        source_hashes: &[],
        transitive_dep_hashes: &[],
        trustc_fingerprint: "test-fingerprint",
        dmath_versions: &[],
        verification_policy: &policy,
        target_triple: "aarch64-apple-darwin",
        profile: "dev",
        codegen_flags: &[],
        rustc_version: "1.0.0",
        edition: "2024",
    };
    CacheKey::compute(&inputs)
}

fn artifact(dir: &std::path::Path, name: &str, body: &[u8]) -> PathBuf {
    let p = dir.join(name);
    std::fs::write(&p, body).expect("write artifact");
    p
}

fn populate(cache: &BuildCache, key: &CacheKey, src_dir: &std::path::Path, label: &str) {
    let req = StoreRequest {
        rlib_source: artifact(src_dir, &format!("lib-{label}.rlib"), b"rlib-content"),
        rmeta_source: artifact(src_dir, &format!("lib-{label}.rmeta"), b"rmeta-content"),
        depfile_source: artifact(src_dir, &format!("lib-{label}.d"), b"depfile"),
        certificate_source: artifact(
            src_dir,
            &format!("cert-{label}.json"),
            b"{\"verified\":true}",
        ),
    };
    cache.store(key, req).expect("store");
}

#[test]
fn rlib_swap_after_store_is_caught_by_seal_on_next_lookup() {
    let tmp = TempDir::new().unwrap();
    let cache_root = tmp.path().join("cache");
    let src = tmp.path().join("src");
    std::fs::create_dir_all(&src).unwrap();
    let cache = BuildCache::open(&cache_root).expect("open cache");

    let key = key_for("policy-A");
    populate(&cache, &key, &src, "A");

    // First lookup succeeds.
    assert!(cache.lookup(&key).expect("lookup ok").is_some());

    // An out-of-band writer changes the cached rlib without updating the tag.
    let entry_dir = cache.root().join("objects").join(&key.hex()[..2]).join(&key.hex()[2..]);
    std::fs::write(entry_dir.join("rlib"), b"malicious-rlib-content").unwrap();

    // Next lookup MUST miss because the HMAC seal no longer verifies.
    assert!(
        cache.lookup(&key).expect("lookup ok").is_none(),
        "tampered rlib must invalidate the seal on subsequent lookups"
    );
}

#[test]
fn certificate_removal_after_store_is_treated_as_miss() {
    let tmp = TempDir::new().unwrap();
    let cache_root = tmp.path().join("cache");
    let src = tmp.path().join("src");
    std::fs::create_dir_all(&src).unwrap();
    let cache = BuildCache::open(&cache_root).expect("open cache");

    let key = key_for("policy-B");
    populate(&cache, &key, &src, "B");

    // An out-of-band writer deletes the certificate, leaving the rlib in place.
    let entry_dir = cache.root().join("objects").join(&key.hex()[..2]).join(&key.hex()[2..]);
    std::fs::remove_file(entry_dir.join("certificate.json")).unwrap();

    // Lookup MUST miss -- pure binary hits without a certificate are
    // never served.
    assert!(
        cache.lookup(&key).expect("lookup ok").is_none(),
        "binary present without certificate must not be served"
    );
}

#[test]
fn gc_evicts_tampered_entries_first() {
    let tmp = TempDir::new().unwrap();
    let cache_root = tmp.path().join("cache");
    let src = tmp.path().join("src");
    std::fs::create_dir_all(&src).unwrap();
    let cache = BuildCache::open(&cache_root).expect("open cache");

    let k_good = key_for("policy-good");
    let k_bad = key_for("policy-bad");
    populate(&cache, &k_good, &src, "good");
    populate(&cache, &k_bad, &src, "bad");

    // Tamper with the second entry's rlib.
    let bad_dir = cache.root().join("objects").join(&k_bad.hex()[..2]).join(&k_bad.hex()[2..]);
    std::fs::write(bad_dir.join("rlib"), b"tampered").unwrap();

    // Pre-gc: stats sees 2 entries.
    assert_eq!(cache.stats().expect("stats").entries, 2);

    // gc with infinite cap evicts the tampered entry as corrupt; the
    // good entry survives.
    let report = cache.gc(u64::MAX).expect("gc");
    assert_eq!(report.entries_evicted, 1, "gc must eagerly remove the corrupt entry");
    assert!(cache.lookup(&k_good).expect("lookup ok").is_some(), "good entry survives");
    assert!(cache.lookup(&k_bad).expect("lookup ok").is_none(), "bad entry not served");
}

#[test]
fn stats_reflects_store_and_eviction() {
    let tmp = TempDir::new().unwrap();
    let cache_root = tmp.path().join("cache");
    let src = tmp.path().join("src");
    std::fs::create_dir_all(&src).unwrap();
    let cache = BuildCache::open(&cache_root).expect("open cache");

    let before = cache.stats().expect("stats");
    assert_eq!(before.entries, 0);
    assert_eq!(before.total_bytes, 0);

    let k1 = key_for("policy-1");
    let k2 = key_for("policy-2");
    populate(&cache, &k1, &src, "1");
    populate(&cache, &k2, &src, "2");

    let after = cache.stats().expect("stats");
    assert_eq!(after.entries, 2);
    assert!(after.total_bytes > 0);

    // Force eviction by setting a tiny cap.
    let _ = cache.gc(1).expect("gc");
    let post_gc = cache.stats().expect("stats");
    assert!(post_gc.entries < after.entries, "gc should have evicted entries");
}
