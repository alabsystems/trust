//! `cargo run --example full_lifecycle` — standalone demonstration of the
//! experimental cache API: compute a prototype key, store simulated bytes, and
//! retrieve an artifact candidate. This is not a production compiler or proof
//! validation integration.
//!
//! Runs against a temp dir so it doesn't interact with the user's real
//! ~/.trust/cache. Useful as a smoke check and as documentation.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;

use trust_buildcache::{BuildCache, CacheInputs, CacheKey, StoreRequest};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1) Pick an isolated demonstration cache root.
    let demo_root = std::env::temp_dir().join("trust-buildcache-demo");
    let _ = std::fs::remove_dir_all(&demo_root);
    let cache = BuildCache::open(&demo_root)?;
    println!("cache root: {}", cache.root().display());

    // 2) Build the prototype CacheInputs. It deliberately does not represent
    //    Cargo's complete resolved unit graph.
    let policy = "L0+strict".to_string();
    let inputs = CacheInputs {
        source_hashes: &[],
        transitive_dep_hashes: &[],
        trustc_fingerprint: "demo-trustc-1.0",
        dmath_versions: &[("ay".to_string(), "0.10".to_string())],
        verification_policy: &policy,
        target_triple: "aarch64-apple-darwin",
        profile: "dev",
        codegen_flags: &[],
        rustc_version: "1.0.0",
        edition: "2024",
    };
    let key = CacheKey::compute(&inputs);
    println!("cache key: {}", key.hex());

    // 3) Lookup: first invocation misses.
    let pre = cache.lookup(&key)?;
    assert!(pre.is_none(), "first lookup must miss");
    println!("lookup #1: MISS (expected)");

    // 4) Simulate compiler artifacts; no verification occurs in this example.
    let stage = demo_root.join("stage");
    std::fs::create_dir_all(&stage)?;
    let rlib = stage.join("libfoo.rlib");
    let rmeta = stage.join("libfoo.rmeta");
    let depfile = stage.join("libfoo.d");
    let cert = stage.join("libfoo.trust-cert.json");
    std::fs::write(&rlib, b"rlib-bytes")?;
    std::fs::write(&rmeta, b"rmeta-bytes")?;
    std::fs::write(&depfile, b"depfile-content")?;
    std::fs::write(&cert, b"{\"demo_only\":true,\"evidentiary\":false}")?;

    // 5) Store the simulated artifacts and certificate-shaped sidecar.
    cache.store(
        &key,
        StoreRequest {
            rlib_source: rlib,
            rmeta_source: rmeta,
            depfile_source: depfile,
            certificate_source: cert,
        },
    )?;
    println!("store:     OK");

    // 6) Lookup again: an integrity-checked, non-evidentiary candidate exists.
    let post = cache.lookup(&key)?.ok_or("expected candidate after store")?;
    println!("lookup #2: CANDIDATE (live validation still required)");
    println!("  rlib:       {}", post.rlib.display());
    println!("  rmeta:      {}", post.rmeta.display());
    println!("  certificate:{}", post.certificate.display());
    println!("  hit_count:  {}", post.metadata.hit_count);

    // 7) Show stats.
    let stats = cache.stats()?;
    println!("stats: {} entries, {} bytes", stats.entries, stats.total_bytes);

    // 8) Demonstrate corruption detection: alter the rlib, next lookup misses.
    std::fs::write(post.rlib.clone(), b"corrupted-payload")?;
    let after_tamper: Option<_> = cache.lookup(&key)?;
    assert!(
        after_tamper.is_none(),
        "modified cache entry must not be returned (HMAC seal mismatch)"
    );
    println!("post-corruption lookup: MISS (HMAC seal detected modified bytes)");

    // Cleanup demo dir.
    let _ = std::fs::remove_dir_all(&demo_root);
    println!("demo complete");

    // Suppress an unused warning since this is the demo path only.
    let _ = PathBuf::new();
    Ok(())
}
