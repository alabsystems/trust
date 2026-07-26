//! `targo trust cache` subcommand implementations.
//!
//! Exposes the `trust-buildcache` operations to end users:
//!
//! - `targo trust cache stats` — entry count, total size, root path.
//! - `targo trust cache gc [--max-size BYTES]` — run LRU GC.
//! - `targo trust cache clear` — remove all entries.
//! - `targo trust cache info <key-hex>` — show metadata for one key.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::process::ExitCode;

use trust_buildcache::{BuildCache, CacheKey};

pub(crate) fn usage_text() -> &'static str {
    "Usage: targo trust cache <stats|gc|clear|info>\n\
\n\
Commands:\n\
  stats                  Print build-cache entries, total size, root path\n\
  gc [--max-size BYTES]  LRU evict build-cache entries to fit cap\n\
  clear --yes            Wipe the build-cache after explicit confirmation\n\
  info <key-hex>         Print validated merged metadata for one build-cache entry\n\
\n\
The artifact-candidate cache is not consumed by the production compiler.\n\
These commands only inspect or maintain explicitly populated experimental entries.\n"
}

/// Print stats for the buildcache at the default root.
pub(crate) fn run_stats() -> ExitCode {
    let root = BuildCache::default_root();
    println!("trust-buildcache root: {}", root.display());

    let cache = match BuildCache::open_existing(&root) {
        Ok(Some(cache)) => cache,
        Ok(None) => {
            println!("entries:    0");
            println!("total size: 0 bytes (0.00 MiB)");
            println!("last gc:    never");
            return ExitCode::SUCCESS;
        }
        Err(e) => {
            eprintln!("error: failed to open cache at {}: {e}", root.display());
            return ExitCode::FAILURE;
        }
    };
    let stats = match cache.stats() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: failed to read cache stats: {e}");
            return ExitCode::FAILURE;
        }
    };

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
    ExitCode::SUCCESS
}

/// Run LRU eviction. `max_size_bytes` defaults to 20 GiB if `None`.
pub(crate) fn run_gc(max_size_bytes: Option<u64>) -> ExitCode {
    let root = BuildCache::default_root();
    let cache = match BuildCache::open(&root) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: failed to open cache at {}: {e}", root.display());
            return ExitCode::FAILURE;
        }
    };
    let cap = max_size_bytes.unwrap_or(20 * 1024 * 1024 * 1024); // 20 GiB
    match cache.gc(cap) {
        Ok(report) => {
            println!(
                "evicted {} entries, freed {} bytes ({:.2} MiB)",
                report.entries_evicted,
                report.bytes_freed,
                report.bytes_freed as f64 / (1024.0 * 1024.0)
            );
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("error: gc failed: {e}");
            ExitCode::FAILURE
        }
    }
}

/// Remove all entries by deleting the `objects/` subdir.
///
/// Returns early without removing anything if the cache root doesn't
/// exist or `confirm` is `false`.
pub(crate) fn run_clear(confirm: bool) -> ExitCode {
    if !confirm {
        eprintln!("refusing to clear cache without confirmation; pass --yes to proceed");
        return ExitCode::FAILURE;
    }
    let root = BuildCache::default_root();
    let objects = root.join("objects");
    match std::fs::symlink_metadata(&objects) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            println!("cache at {} is already empty", root.display());
            return ExitCode::SUCCESS;
        }
        Err(error) => {
            eprintln!("error: failed to inspect cache at {}: {error}", objects.display());
            return ExitCode::FAILURE;
        }
        Ok(_) => {}
    }
    let cache = match BuildCache::open(&root) {
        Ok(cache) => cache,
        Err(error) => {
            eprintln!("error: failed to open cache at {}: {error}", root.display());
            return ExitCode::FAILURE;
        }
    };
    match cache.clear() {
        Ok(()) => {
            println!("cleared cache at {}", root.display());
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: failed to clear cache at {}: {error}", objects.display());
            ExitCode::FAILURE
        }
    }
}

/// Print metadata for the entry keyed by `hex` (64 lowercase hex chars).
pub(crate) fn run_info(hex: &str) -> ExitCode {
    let Some(key) = parse_cache_key(hex) else {
        eprintln!("error: key must be exactly 64 lowercase hex characters");
        return ExitCode::FAILURE;
    };

    let root = BuildCache::default_root();
    let cache = match BuildCache::open_existing(&root) {
        Ok(Some(cache)) => cache,
        Ok(None) => {
            println!("no complete, integrity-valid entry for key {hex}");
            return ExitCode::SUCCESS;
        }
        Err(error) => {
            eprintln!("error: failed to open cache at {}: {error}", root.display());
            return ExitCode::FAILURE;
        }
    };
    let entry = match cache.inspect(&key) {
        Ok(Some(entry)) => entry,
        Ok(None) => {
            println!("no complete, integrity-valid entry for key {hex}");
            return ExitCode::SUCCESS;
        }
        Err(error) => {
            eprintln!("error: failed to inspect key {hex}: {error}");
            return ExitCode::FAILURE;
        }
    };
    match serde_json::to_string_pretty(&entry.metadata) {
        Ok(metadata) => println!("{metadata}"),
        Err(error) => {
            eprintln!("error: failed to render metadata for key {hex}: {error}");
            return ExitCode::FAILURE;
        }
    }
    ExitCode::SUCCESS
}

fn parse_cache_key(hex: &str) -> Option<CacheKey> {
    if hex.len() != 64
        || !hex.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (index, chunk) in hex.as_bytes().chunks_exact(2).enumerate() {
        let pair = std::str::from_utf8(chunk).ok()?;
        bytes[index] = u8::from_str_radix(pair, 16).ok()?;
    }
    Some(CacheKey::from_bytes(bytes))
}

/// Parse the args after `targo trust cache` and dispatch.
///
/// Recognized commands:
///   stats
///   gc [--max-size BYTES]
///   clear --yes
///   info <hex>
pub(crate) fn dispatch(args: &[String]) -> ExitCode {
    let (cmd, rest) = match args.split_first() {
        Some((c, r)) => (c.as_str(), r),
        None => {
            eprint!("{}", usage_text());
            return ExitCode::FAILURE;
        }
    };
    match cmd {
        "help" | "-h" | "--help" => {
            print!("{}", usage_text());
            ExitCode::SUCCESS
        }
        "stats" if rest.is_empty() => run_stats(),
        "stats" => invalid_args("usage: targo trust cache stats"),
        "gc" => match parse_max_size_flag(rest) {
            Ok(max_size) => run_gc(max_size),
            Err(error) => invalid_args(&error),
        },
        "clear" => {
            if matches!(rest, [flag] if flag == "--yes" || flag == "-y") {
                run_clear(true)
            } else {
                invalid_args("usage: targo trust cache clear --yes")
            }
        }
        "info" if rest.len() == 1 => run_info(&rest[0]),
        "info" => invalid_args("usage: targo trust cache info <hex>"),
        other => {
            eprintln!("unknown cache subcommand: {other}");
            eprint!("{}", usage_text());
            ExitCode::FAILURE
        }
    }
}

fn invalid_args(message: &str) -> ExitCode {
    eprintln!("error: {message}");
    ExitCode::FAILURE
}

/// Extract `--max-size BYTES` from a flag slice. Returns `None` if absent
/// or malformed.
fn parse_max_size_flag(args: &[String]) -> Result<Option<u64>, String> {
    match args {
        [] => Ok(None),
        [flag, value] if flag == "--max-size" => value.parse().map(Some).map_err(|_| {
            format!("invalid --max-size value `{value}`; expected an unsigned integer")
        }),
        [joined] if joined.starts_with("--max-size=") => {
            let value = joined.trim_start_matches("--max-size=");
            value.parse().map(Some).map_err(|_| {
                format!("invalid --max-size value `{value}`; expected an unsigned integer")
            })
        }
        _ => Err("usage: targo trust cache gc [--max-size BYTES]".to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_max_size_flag_handles_spaced_value() {
        let args = vec!["--max-size".to_string(), "1024".to_string()];
        assert_eq!(parse_max_size_flag(&args), Ok(Some(1024)));
    }

    #[test]
    fn parse_max_size_flag_handles_equals_value() {
        let args = vec!["--max-size=2048".to_string()];
        assert_eq!(parse_max_size_flag(&args), Ok(Some(2048)));
    }

    #[test]
    fn parse_max_size_flag_missing_returns_none() {
        let args: Vec<String> = vec![];
        assert_eq!(parse_max_size_flag(&args), Ok(None));
    }

    #[test]
    fn parse_max_size_flag_rejects_malformed_and_unknown_values() {
        assert!(parse_max_size_flag(&["--max-size=nope".to_string()]).is_err());
        assert!(parse_max_size_flag(&["--unknown".to_string()]).is_err());
        assert!(parse_max_size_flag(&["--max-size".to_string()]).is_err());
    }

    #[test]
    fn cache_key_parser_requires_canonical_lowercase_hex() {
        let canonical = "abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789";
        assert_eq!(parse_cache_key(canonical).unwrap().hex(), canonical);
        assert!(parse_cache_key(&canonical.to_ascii_uppercase()).is_none());
        assert!(parse_cache_key("abc").is_none());
    }

    #[test]
    fn usage_text_names_cache_subcommands() {
        let usage = usage_text();
        assert!(usage.contains("Usage: targo trust cache"));
        for expected in ["stats", "gc [--max-size BYTES]", "clear --yes", "info <key-hex>"] {
            assert!(usage.contains(expected), "missing `{expected}` in {usage}");
        }
    }
}
