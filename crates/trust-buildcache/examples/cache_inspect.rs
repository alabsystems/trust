//! `cargo run --example cache_inspect` — inspect a trust-buildcache root.
//!
//! Prints stats for the cache at `$TRUST_CACHE_DIR` (default
//! `~/.trust/cache`). Useful for inspecting explicitly populated experimental
//! entries and as a worked example of the public maintenance API. The
//! production compiler does not consume this cache.
//!
//! Usage:
//!   cargo run --example cache_inspect
//!   TRUST_CACHE_DIR=/tmp/my-cache cargo run --example cache_inspect
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_buildcache::BuildCache;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = BuildCache::default_root();
    println!("cache root: {}", root.display());

    let cache = BuildCache::open(&root)?;
    let stats = cache.stats()?;

    println!("entries:    {}", stats.entries);
    println!(
        "total size: {} bytes ({:.2} MiB)",
        stats.total_bytes,
        stats.total_bytes as f64 / (1024.0 * 1024.0)
    );
    if let Some(ts) = stats.last_gc_unix_ms {
        println!("last gc:    {ts} (unix ms)");
    } else {
        println!("last gc:    never");
    }

    Ok(())
}
