//! Content and solver fingerprints used as cache keys.
//!
//! - [`compute_content_hash`] hashes the function body + contracts + spec.
//!   It delegates to [`VerifiableFunction::content_hash`] so the cache and
//!   the verifier always agree on the key (regression test in `cache.rs`).
//! - [`compute_solver_fingerprint`] hashes the configured solver toolchain
//!   (name + a content digest of the binary). Out-of-process solver rebuilds
//!   rotate this value so cached proofs from an older ay are not silently
//!   reused (#479 / cache v5). The digest is over the binary's *contents*, not
//!   its path or mtime, so the same solver build produces the same fingerprint
//!   on every machine — a prerequisite for sharing cache entries across a team
//!   or CI fleet.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fs::{File, OpenOptions};
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::Path;
use std::time::{SystemTime, UNIX_EPOCH};

use sha2::{Digest, Sha256};
use trust_types::VerifiableFunction;

/// A strong, path-independent identity for one solver binary.
///
/// Both fields are SHA-256 hex strings. `content_digest` identifies the exact
/// bytes read from the binary. `cache_key` additionally domains the digest by
/// the solver name and this crate's cache-schema implementation version.
/// Neither field contains the installation path, so moving byte-identical
/// solver binaries does not invalidate otherwise equivalent cache keys.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolverBinaryFingerprint {
    content_digest: String,
    cache_key: String,
}

impl SolverBinaryFingerprint {
    /// SHA-256 of the solver binary's complete contents.
    #[must_use]
    pub fn content_digest(&self) -> &str {
        &self.content_digest
    }

    /// Path-independent cache/semantics key for this solver build.
    #[must_use]
    pub fn cache_key(&self) -> &str {
        &self.cache_key
    }
}

/// Read and strongly fingerprint a solver binary.
///
/// An I/O failure is returned to the caller; there is deliberately no
/// metadata/size/path fallback. Size is not a cryptographic identity (two
/// different binaries commonly have the same length), and accepting such a
/// fallback could make a persistent proof cache collide across solver builds.
pub fn fingerprint_solver_binary(
    solver_name: &str,
    solver_path: &Path,
) -> std::io::Result<SolverBinaryFingerprint> {
    let content_digest = solver_content_digest(solver_path)?;
    Ok(fingerprint_from_content_digest(solver_name, content_digest))
}

/// Copy a solver into a new immutable execution snapshot while fingerprinting
/// the exact bytes written.
///
/// The destination is opened with `create_new`, so an existing file or symlink
/// is never followed or truncated. Each source chunk is written to the snapshot
/// and fed to SHA-256 in the same loop. Consequently the returned identity is
/// the identity of the executable snapshot even if the source pathname is
/// concurrently replaced or its contents change during the copy. Callers can
/// safely use `snapshot_path` for execution and the returned key for cache
/// semantics without a hash-then-path-exec TOCTOU window.
///
/// On failure, any partial destination is removed. The source must be a regular
/// executable file on Unix; the private snapshot is owner-readable/executable
/// and deliberately not writable.
pub fn snapshot_solver_binary(
    solver_name: &str,
    solver_path: &Path,
    snapshot_path: &Path,
) -> std::io::Result<SolverBinaryFingerprint> {
    let source = File::open(solver_path)?;
    let metadata = source.metadata()?;
    if !metadata.is_file() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "solver path is not a regular file",
        ));
    }

    let mut options = OpenOptions::new();
    options.create_new(true).write(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};

        let mode = metadata.permissions().mode() & 0o777;
        if mode & 0o111 == 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::PermissionDenied,
                "solver file is not executable",
            ));
        }
        // The private snapshot is an execution artifact, not a staging file.
        // Remove all write bits once its create-only descriptor is closed so
        // ordinary source rebuilds or accidental path writes cannot drift it.
        options.mode(0o500);
    }

    // APFS fast path: a copy-on-write CLONE materializes the full snapshot in
    // constant time with ZERO data writes — the byte-for-byte copy loop below
    // wrote the whole solver (~95 MB) per COMPILE, which is both a real cost
    // (a 272-fixture falsification run copies ~26 GB) and a spurious SIGXFSZ
    // under any RLIMIT_FSIZE harness (the falsification gate's `ulimit -f`
    // killed every fixture once the solver binary crossed the cap; a clone
    // performs no extending write and is exempt — verified empirically under
    // `ulimit -f 1024`). The TOCTOU property is preserved: the clone's content
    // is FIXED at clone time (source modifications never propagate through an
    // APFS clone), `clonefile` refuses an existing destination exactly like
    // `create_new`, and the fingerprint hashes the CLONE's own bytes — still
    // "the identity of the executable snapshot". Any clone failure (non-APFS
    // volume, cross-device, older OS) falls back to the copy loop unchanged.
    #[cfg(target_os = "macos")]
    if clone_solver_snapshot(solver_path, snapshot_path).is_ok() {
        let result = solver_content_digest(snapshot_path)
            .map(|digest| fingerprint_from_content_digest(solver_name, digest));
        if result.is_err() {
            let _ = std::fs::remove_file(snapshot_path);
        }
        return result;
    }

    let snapshot = options.open(snapshot_path)?;
    let result = copy_and_fingerprint_solver(solver_name, source, snapshot);
    if result.is_err() {
        let _ = std::fs::remove_file(snapshot_path);
    }
    result
}

/// APFS copy-on-write snapshot of the solver binary. The destination must not
/// exist (`clonefile` refuses, mirroring `create_new`); the clone is then
/// stripped to owner read+execute, matching the copy path's `mode(0o500)`
/// snapshot discipline. `CLONE_NOFOLLOW` refuses a symlinked SOURCE, closing
/// the same recheck race the copy path's open+metadata sequence closes.
#[cfg(target_os = "macos")]
fn clone_solver_snapshot(source: &Path, destination: &Path) -> std::io::Result<()> {
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::fs::PermissionsExt;

    unsafe extern "C" {
        fn clonefile(
            src: *const std::ffi::c_char,
            dst: *const std::ffi::c_char,
            flags: std::ffi::c_int,
        ) -> std::ffi::c_int;
    }
    // `CLONE_NOFOLLOW` from `<sys/clonefile.h>`.
    const CLONE_NOFOLLOW: std::ffi::c_int = 0x0001;

    let src = std::ffi::CString::new(source.as_os_str().as_bytes())
        .map_err(|_| std::io::Error::from(std::io::ErrorKind::InvalidInput))?;
    let dst = std::ffi::CString::new(destination.as_os_str().as_bytes())
        .map_err(|_| std::io::Error::from(std::io::ErrorKind::InvalidInput))?;
    let rc = unsafe { clonefile(src.as_ptr(), dst.as_ptr(), CLONE_NOFOLLOW) };
    if rc != 0 {
        return Err(std::io::Error::last_os_error());
    }
    std::fs::set_permissions(destination, std::fs::Permissions::from_mode(0o500))
}

fn fingerprint_from_content_digest(
    solver_name: &str,
    content_digest: [u8; 32],
) -> SolverBinaryFingerprint {
    let mut hasher = Sha256::new();
    hasher.update(env!("CARGO_PKG_VERSION").as_bytes());
    hasher.update(b"|solver:");
    hasher.update(solver_name.as_bytes());
    hasher.update(b"|content:");
    hasher.update(content_digest);
    SolverBinaryFingerprint {
        content_digest: hex_digest(&content_digest),
        cache_key: format!("{:x}", hasher.finalize()),
    }
}

/// Fingerprint of the solver toolchain a cached entry was produced under.
///
/// Combines the `trust-cache` crate version with the configured solver
/// binary's *content digest*. A solver rebuild changes the binary's bytes,
/// which rotates the fingerprint and forces re-verification of dependent
/// entries.
///
/// The fingerprint is **machine-independent by construction**: it deliberately
/// excludes the binary's path and mtime (both of which vary across machines
/// for the same logical build), so two installations of byte-identical solver
/// binaries produce the same fingerprint. This is what lets cache entries be
/// shared across machines without falsely diverging.
///
/// `solver_name` identifies the primary solver (e.g., `"ay"`). `solver_path`
/// is the resolved path to its binary. `None` means no solver is configured;
/// an unreadable path also returns `None`. In either case a caller MUST treat
/// persistent proof caching as ineligible rather than inventing a weaker key.
#[must_use]
pub fn compute_solver_fingerprint(solver_name: &str, solver_path: Option<&Path>) -> Option<String> {
    let path = solver_path?;
    fingerprint_solver_binary(solver_name, path).ok().map(|identity| identity.cache_key)
}

/// SHA-256 of the file's contents, streamed so a large solver binary is never
/// fully buffered in memory. Returns an I/O error if any byte cannot be read.
fn solver_content_digest(path: &Path) -> std::io::Result<[u8; 32]> {
    let file = File::open(path)?;
    let mut reader = BufReader::new(file);
    let mut hasher = Sha256::new();
    let mut buf = [0u8; 64 * 1024];
    loop {
        match reader.read(&mut buf)? {
            0 => break,
            n => hasher.update(&buf[..n]),
        }
    }
    Ok(hasher.finalize().into())
}

fn copy_and_fingerprint_solver(
    solver_name: &str,
    source: File,
    snapshot: File,
) -> std::io::Result<SolverBinaryFingerprint> {
    let mut reader = BufReader::new(source);
    let mut writer = BufWriter::new(snapshot);
    let mut hasher = Sha256::new();
    let mut buf = [0u8; 64 * 1024];
    loop {
        match reader.read(&mut buf)? {
            0 => break,
            n => {
                writer.write_all(&buf[..n])?;
                hasher.update(&buf[..n]);
            }
        }
    }
    writer.flush()?;
    writer.get_ref().sync_all()?;
    Ok(fingerprint_from_content_digest(solver_name, hasher.finalize().into()))
}

fn hex_digest(digest: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    use std::fmt::Write as _;
    for byte in digest {
        write!(&mut out, "{byte:02x}").expect("writing to String cannot fail");
    }
    out
}

/// Compute a SHA-256 content hash of a function's body, contracts, and spec.
///
/// This is the cache key: if the hash matches a stored entry, the function
/// has not changed and verification can be skipped.
///
/// Delegates to [`VerifiableFunction::content_hash()`] to ensure a single
/// source of truth. The two must always agree.
#[must_use]
pub fn compute_content_hash(func: &VerifiableFunction) -> String {
    func.content_hash()
}

/// Current Unix timestamp in seconds.
pub(crate) fn now_unix_secs() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

/// The stable verification-semantics segment recording whether the crate being
/// compiled is a *whole-program* artifact (executable / staticlib / cdylib)
/// rather than a downstream-extensible one (rlib / dylib / proc-macro).
///
/// Some obligations are discharged using facts that hold only for a closed
/// compilation. The canonical case is dyn-dispatch trait sealedness: a local
/// trait with no blanket impls has a fully known impl set only when every crate
/// type is whole-program — for an `rlib` a downstream crate may still add a
/// non-conforming impl, so the trait is open and a dyn-dispatch postcondition
/// may not strengthen caller VCs. The same function, byte-identical body,
/// contracts, and solver, can therefore legitimately prove when compiled into a
/// `bin` and must not prove when compiled into an `rlib`. Omitting the bit would
/// let one key serve both, so it belongs in the key rather than in a caller's
/// discipline.
///
/// Deliberately coarse — one boolean, not the crate-type list — so two
/// whole-program shapes (`[Executable]` vs `[StaticLib, Cdylib]`) that are
/// equivalent for sealedness still share a key, while a whole-program shape can
/// never alias a downstream-extensible one.
#[must_use]
pub fn whole_program_semantics_segment(whole_program: bool) -> String {
    format!("whole_program={whole_program}")
}

/// Append the whole-program segment to a verification-semantics key.
///
/// Every producer of such a key composes it here so the folding is
/// byte-identical across them; a second spelling would silently create two key
/// spaces for the same semantics.
#[must_use]
pub fn compose_semantics_key(base_semantics_key: &str, whole_program: bool) -> String {
    format!("{base_semantics_key};{}", whole_program_semantics_segment(whole_program))
}

#[cfg(test)]
mod semantics_key_tests {
    use super::{compose_semantics_key, whole_program_semantics_segment};

    #[test]
    fn whole_program_shape_cannot_alias_a_downstream_extensible_one() {
        let base = "v3;mode=Full;level=1";
        let bin = compose_semantics_key(base, true);
        let rlib = compose_semantics_key(base, false);
        assert_ne!(bin, rlib);
        assert!(bin.starts_with(base) && rlib.starts_with(base));
        assert!(bin.ends_with(&whole_program_semantics_segment(true)));
        assert!(rlib.ends_with(&whole_program_semantics_segment(false)));
        assert_eq!(compose_semantics_key(base, true), bin);
    }
}
