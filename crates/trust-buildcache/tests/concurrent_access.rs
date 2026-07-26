//! Multi-threaded stress tests for the cache. The cache uses per-entry
//! content-addressed directories, so concurrent stores under DIFFERENT
//! keys must never collide; concurrent stores of the SAME key serialize
//! (first completed writer wins) and must all succeed without corrupting the
//! entry. Concurrent
//! LOOKUPS on the same key must all succeed -- LRU bookkeeping lives in
//! an unsealed sidecar (`access.txt`) so reader contention can't
//! invalidate the HMAC.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;
use std::sync::Arc;
use std::thread;

use tempfile::TempDir;
use trust_buildcache::{BuildCache, CacheInputs, CacheKey, StoreRequest};

fn key_for(label: &str) -> CacheKey {
    let policy = label.to_string();
    let inputs = CacheInputs {
        source_hashes: &[],
        transitive_dep_hashes: &[],
        trustc_fingerprint: "test",
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

fn store_req(src_dir: &std::path::Path, tag: &str) -> StoreRequest {
    StoreRequest {
        rlib_source: artifact(src_dir, &format!("rlib-{tag}"), b"rlib"),
        rmeta_source: artifact(src_dir, &format!("rmeta-{tag}"), b"rmeta"),
        depfile_source: artifact(src_dir, &format!("d-{tag}"), b"d"),
        certificate_source: artifact(src_dir, &format!("cert-{tag}.json"), b"{}"),
    }
}

#[test]
fn concurrent_stores_under_distinct_keys_dont_corrupt_each_other() {
    let tmp = TempDir::new().unwrap();
    let cache = Arc::new(BuildCache::open(tmp.path().join("cache")).expect("open"));
    let src_root = Arc::new(tmp.path().join("src"));
    std::fs::create_dir_all(&*src_root).unwrap();

    let mut handles = Vec::new();
    for i in 0..16 {
        let cache = Arc::clone(&cache);
        let src_root = Arc::clone(&src_root);
        handles.push(thread::spawn(move || {
            let thread_src = src_root.join(format!("t{i}"));
            std::fs::create_dir_all(&thread_src).unwrap();
            let key = key_for(&format!("policy-{i}"));
            cache.store(&key, store_req(&thread_src, &format!("t{i}"))).expect("store");
            assert!(cache.lookup(&key).expect("lookup").is_some());
        }));
    }
    for h in handles {
        h.join().expect("thread");
    }

    // All 16 entries must exist and be retrievable.
    let stats = cache.stats().expect("stats");
    assert_eq!(stats.entries, 16);
    for i in 0..16 {
        let key = key_for(&format!("policy-{i}"));
        assert!(
            cache.lookup(&key).expect("lookup").is_some(),
            "key {i} should still resolve after concurrent stores"
        );
    }
}

#[test]
fn concurrent_stores_under_the_same_key_serialize_without_partial_errors() {
    let tmp = TempDir::new().unwrap();
    let cache = Arc::new(BuildCache::open(tmp.path().join("cache")).expect("open"));
    let src_root = Arc::new(tmp.path().join("src"));
    std::fs::create_dir_all(&*src_root).unwrap();
    let key = key_for("shared-policy");

    let mut handles = Vec::new();
    for i in 0..16 {
        let cache = Arc::clone(&cache);
        let src_root = Arc::clone(&src_root);
        let key = key;
        handles.push(thread::spawn(move || {
            let thread_src = src_root.join(format!("same-{i}"));
            std::fs::create_dir_all(&thread_src).unwrap();
            cache
                .store(&key, store_req(&thread_src, &format!("same-{i}")))
                .expect("same-key store must wait for and accept the first complete entry");
        }));
    }
    for handle in handles {
        handle.join().expect("thread");
    }

    assert!(cache.lookup(&key).expect("lookup").is_some());
    assert_eq!(cache.stats().expect("stats").entries, 1);
}

#[test]
fn concurrent_lookups_on_same_key_all_hit() {
    // Pre-split, this test failed because lookup re-sealed the HMAC after
    // bumping last_access / hit_count inside metadata.json. Two readers
    // racing on the read/write/seal sequence would have one see a stale
    // HMAC and report a (false) miss.
    //
    // Post-split, LRU bookkeeping is in `access.txt` outside the HMAC
    // scope: readers all observe a stable seal and never report a miss
    // for a sealed entry on their account. Lost hit_count increments are
    // acceptable; spurious misses are not.
    let tmp = TempDir::new().unwrap();
    let cache = Arc::new(BuildCache::open(tmp.path().join("cache")).expect("open"));
    let src_root = tmp.path().join("src");
    std::fs::create_dir_all(&src_root).unwrap();
    let key = key_for("hot-key");
    cache.store(&key, store_req(&src_root, "hot")).expect("store");

    const READERS: usize = 16;
    const LOOKUPS_PER_READER: usize = 32;

    let mut handles = Vec::new();
    for _ in 0..READERS {
        let cache = Arc::clone(&cache);
        let key = key.clone();
        handles.push(thread::spawn(move || {
            let mut hits = 0usize;
            for _ in 0..LOOKUPS_PER_READER {
                if cache.lookup(&key).expect("lookup").is_some() {
                    hits += 1;
                }
            }
            hits
        }));
    }
    let total_hits: usize = handles.into_iter().map(|h| h.join().expect("thread")).sum();

    // Every single lookup -- across all readers -- must report a hit.
    // A spurious miss here means the HMAC was invalidated by concurrent
    // LRU bookkeeping, which is exactly the bug the split fixes.
    assert_eq!(
        total_hits,
        READERS * LOOKUPS_PER_READER,
        "concurrent same-key lookups must never report a spurious miss"
    );

    // The entry must still be retrievable after the storm.
    assert!(cache.lookup(&key).expect("lookup").is_some());
}
