// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **Trust-owned operating-system entropy** — the one thing this tree actually
//! needs from a random-number crate, and deliberately nothing else.
//!
//! # Why this crate exists
//!
//! Phase 1b of the third-party replacement program (after `trust-sha2` and
//! `trust-hmac`). Across the whole of `crates/` there is exactly **one**
//! production call into a random-number generator:
//!
//! ```text
//! crates/trust-proof-cert/src/signing.rs:40
//!     let mut rng = rand::thread_rng();
//!     let key = SigningKey::generate(&mut rng);
//! ```
//!
//! and across `targo-trust` there are four, all of them
//! `getrandom::fill(&mut buf)` for a nonce or a verification-session id. Both
//! `rand` and `getrandom` report as `dependency-policy-excluded` in the
//! verified lane, so every proof that names a signed certificate or a
//! verification session is conditional on units Trust does not own. Retiring
//! `rand` also retires `rand_chacha`, `rand_core` and `getrandom` — the last of
//! which drags `wasi` with it — once `ed25519-dalek`'s `rand_core` feature
//! comes off.
//!
//! # The surface is two functions because two functions is what is used
//!
//! [`fill_bytes`] serves the nonce/session-id sites. [`secret_seed_32`] serves
//! the key-generation site. Each has a `try_` twin that returns
//! [`EntropyError`] instead of panicking, because the `targo-trust` sites are
//! inside `Result`-returning functions and the signing site is not.
//!
//! **No `Rng`/`RngCore` trait is provided, and none is needed.** That is a
//! measured claim, not a simplification:
//! `ed25519_dalek::SigningKey::generate` (`signing.rs:202` of
//! `ed25519-dalek-2.2.0`) is, in its entirety,
//!
//! ```text
//! let mut secret = SecretKey::default();   // SecretKey = [u8; 32]
//! csprng.fill_bytes(&mut secret);
//! Self::from_bytes(&secret)
//! ```
//!
//! and `SigningKey::from_bytes` is *already* called at `signing.rs:46` of
//! `trust-proof-cert`. Per RFC 8032 §5.1.5 an Ed25519 secret key **is** 32
//! uniformly random bytes; deriving the scalar and the prefix from them is
//! `from_bytes`'s job. So the rewrite is
//!
//! ```text
//! -   let mut rng = rand::thread_rng();
//! -   let key = SigningKey::generate(&mut rng);
//! +   let key = SigningKey::from_bytes(&trust_rand::secret_seed_32());
//! ```
//!
//! with no trait plumbing anywhere. That the two spellings agree is proved,
//! not assumed, by `tests/ed25519_equivalence.rs`.
//!
//! # Where the entropy comes from, and why not from `std`
//!
//! **Two arms on every supported platform, tried in order, both fail-closed.**
//! Which two is the only thing that varies; the composition that tries them and
//! refuses to invent bytes is platform-independent and lives in `fill_with`.
//! Full platform tables, contracts and citations are in the module docs — `os`
//! and `urandom` for Unix, `windows` for Windows.
//!
//! On **Unix**:
//!
//! 1. **`getentropy(2)`** — the C library function, declared here rather than
//!    imported from `libc` (a declaration is not a dependency). Kernel CSPRNG
//!    on every supported platform; on Linux it blocks until the entropy pool is
//!    initialized; no file descriptor; no userspace state, so no
//!    duplicate-stream-after-`fork()` hazard.
//! 2. **`/dev/urandom`** via `std::fs`, read with `read_exact` so a short read
//!    is an error rather than a silent partial fill. This covers `ENOSYS` on a
//!    pre-3.17 Linux kernel and `EPERM` from a seccomp filter.
//!
//! On **Windows** (minimum Windows 10 version 1809; the `*-win7-windows-*`
//! targets select the legacy pair instead and reach back to Vista):
//!
//! 1. **`ProcessPrng`** from `bcryptprimitives.dll` — the same primitive `std`
//!    itself calls (`library/std/src/sys/random/windows.rs`), declared with a
//!    bare `extern "system"` block and `kind = "raw-dylib"` so that neither
//!    `windows-sys` nor an import library is needed. Documented as infallible;
//!    any return other than `TRUE` is treated as a total failure of this arm.
//! 2. **`BCryptGenRandom`** from `bcrypt.dll` with
//!    `BCRYPT_USE_SYSTEM_PREFERRED_RNG` — a second, independently imported path
//!    to the same system PRNG, checked through `NTSTATUS`.
//!
//! **Windows support is COMPILE-VERIFIED ONLY.** It is type-checked against the
//! real Windows `std` for four MSVC targets and has never been executed; the
//! `windows` module header says so at the top and states exactly what its
//! fallback arm can and cannot rescue.
//!
//! If both fail, [`try_fill_bytes`] returns `Err` and [`fill_bytes`] panics.
//! **There is no path on which this crate returns bytes it did not obtain from
//! the operating system**, which is the single property that matters: a
//! silently weak or zero key is not a degraded outcome, it is a catastrophic
//! one, and it does not announce itself.
//!
//! ## `std::random::SystemRng` was the obvious answer and it is DISQUALIFIED
//!
//! This toolchain has `std::random::SystemRng` behind `#![feature(random)]`,
//! and using it would have meant zero `unsafe`. It cannot be used here, for a
//! reason that was measured rather than guessed:
//!
//! `trust-proof-cert` is reachable from the compiler —
//! `compiler/rustc_mir_transform/Cargo.toml:58` depends on `trust-router`,
//! which depends on `trust-proof-cert` — so this crate is compiled by
//! **stage0** when stage1 is built. The stage0 compiler in this tree is
//! `rustc 1.96.0 (ac68faa20 2026-05-25)`, and the two toolchains disagree about
//! the API:
//!
//! ```text
//! stage0  `use std::random::{Rng, SystemRng};`
//!         error[E0432]: no `SystemRng` in `random` / no `Rng` in `random`
//! stage0  `use std::random::{RandomSource, DefaultRandomSource};`   -> OK
//!
//! stage1  `use std::random::{Rng, SystemRng};`                      -> OK
//! stage1  `use std::random::{RandomSource, DefaultRandomSource};`
//!         error[E0432]: no `DefaultRandomSource` in `random`
//! ```
//!
//! The rename landed in this tree in the upstream port `cdbca2287b`
//! (2026-07-08). There is no spelling of `std::random` that satisfies both
//! compilers, so a crate on the compiler's dependency path cannot use it
//! without a version-conditional or a build script. `getentropy` is the
//! primitive `std` itself reaches on Linux, has been stable ABI since OpenBSD
//! 5.6, and compiles identically on both.
//!
//! # What the tests establish, and what no test can
//!
//! **The tests in this crate establish liveness and plumbing. They do not, and
//! cannot, establish randomness quality.** No unit test can: every finite
//! output of a perfect CSPRNG is also a possible output of a broken one, so a
//! passing statistical test is consistent with a compromised source and a
//! failing one is consistent with a working source. Quality here rests entirely
//! on the operating system's CSPRNG, which is named and cited per platform in
//! the `os`, `urandom` and `windows` module docs, and on the argument — not the
//! assertion — that this crate transports those bytes without corrupting them.
//!
//! What *is* established, by test:
//!
//! * The output of a draw is not all-zero, and successive draws differ
//!   (`tests/liveness.rs`). These catch a dead or stubbed source, which is the
//!   realistic plumbing failure.
//! * Exactly the requested length is written and nothing outside it is touched,
//!   for lengths 0, 1, 31, 32, 33, 255, 256, 257, 4096 (`tests/liveness.rs`).
//! * A single `getentropy` request above the documented 256-byte limit **fails
//!   and leaves the buffer zero**, which is what makes the chunk loop
//!   load-bearing rather than decorative (`os::tests`).
//! * A short read from the fallback arm is an error, not a silent partial fill,
//!   and a missing device is an error (`urandom::tests`). This is the failure
//!   path, exercised.
//! * **The two-arm composition, all four combinations** (`tests`, via the
//!   private `fill_with` seam): a working primary supplies the bytes and the
//!   fallback is never called; a failing primary falls through and the
//!   fallback's bytes are what the caller gets; a broken fallback is masked by a
//!   working primary; and — the case that matters — **both arms failing returns
//!   `Err`, names both arms with their distinct causes, and leaves the
//!   destination buffer untouched rather than zeroing it into something that
//!   looks like a key.** That last path is this crate's central claim and it is
//!   unreachable through the public API on any machine where `getentropy`
//!   works, which is why it is reached through a private parameter.
//! * **The all-zero tripwire fires from the shipped seed path**, not merely from
//!   a direct call to `is_degenerate_seed` (`tests`, via the private
//!   `secret_seed_from` seam) — and a non-degenerate draw reaches the caller
//!   byte-for-byte, including a seed whose only nonzero byte is the last.
//! * The Ed25519 rewrite this crate enables is behaviour-preserving:
//!   `SigningKey::generate(&mut fixed(seed))` and
//!   `SigningKey::from_bytes(&seed)` produce byte-identical secret and public
//!   keys (`tests/ed25519_equivalence.rs`). This is the differential
//!   acceptance gate, and it is exact — unlike the source itself, the *rewrite*
//!   is deterministic and can be compared for equality.
//!
//! # Example
//!
//! ```
//! // A nonce or session id.
//! let mut nonce = [0u8; 16];
//! trust_rand::fill_bytes(&mut nonce);
//!
//! // An Ed25519 secret key seed (RFC 8032 §5.1.5).
//! let seed = trust_rand::secret_seed_32();
//! assert_eq!(seed.len(), 32);
//! ```

// In the SHIPPED build, an entropy arm that nothing references is a build
// error, not a warning.
//
// This closes the last way the fallback arm can be silently retired. The tests
// prove that `fill_with` composes two arms correctly and that both shipped arms
// work; what they cannot observe is `try_fill_bytes` quietly ceasing to *pass*
// the fallback, because on every machine the tests run on the primary arm
// succeeds and the wiring change has no visible effect. Measured: dropping
// `urandom::fill` from `try_fill_bytes`'s argument list left all tests green and
// produced only `warning: function 'fill' is never used`, which
// `warnings = "warn"` does not block.
//
// Under this attribute that same edit fails the build, because `urandom::fill`,
// `urandom::NAME`, `fill_from_path` and `DEVICE` all become unreachable from the
// crate root. `not(test)` scopes it to the shipped build so that a
// work-in-progress test helper does not become a hard error mid-edit.
#![cfg_attr(not(test), deny(dead_code))]

#[cfg(not(any(unix, windows)))]
compile_error!(
    "trust-rand supports Unix and Windows targets. Every entropy arm it has — \
     getentropy(2), /dev/urandom, ProcessPrng, BCryptGenRandom, RtlGenRandom — belongs to \
     one of those two families, and this crate refuses to compile rather than link a \
     source it has no evidence for.\n\
     \n\
     To add a third platform, in order of preference:\n\
     (1) Add an arm pair under src/ behind a #[cfg] for the platform, wire it into the \
         `primary`/`fallback` aliases below, and give it the same evidence the existing \
         arms carry: a documented guarantee, a checked return value, and a test that has \
         been SEEN to fail. Name the OS CSPRNG entry point and cite its contract.\n\
     (2) If this platform does not need certificate signing at all, make the \
         trust-proof-cert dependency on trust-rand #[cfg(any(unix, windows))] and fail \
         closed at the call site instead.\n\
     Do NOT make this crate fall back to a non-OS source anywhere."
);

// ---- platform arm selection --------------------------------------------------
//
// The composition in `fill_with` is platform-independent and refers to the two
// arms ONLY as `primary` and `fallback`. Everything platform-specific is the
// choice of what those two names bind to, which is made here and nowhere else.
// Adding a platform is a `mod` line and an alias pair; it is not an edit to any
// function that handles entropy.
//
// The ordering rule each platform's pair obeys: the PRIMARY is the arm with the
// stronger contract and the fewer moving parts, the FALLBACK is the one that is
// available further back or through a different code path. Per-platform
// justification is in the module headers — `os`/`urandom` for Unix, `windows`
// for Windows, and the latter also states exactly what its fallback can and
// cannot rescue.

#[cfg(unix)]
mod os;
#[cfg(unix)]
mod urandom;

#[cfg(windows)]
mod windows;

// Compiled on Windows because the arms use it, and on any host under `cfg(test)`
// because it is the only part of the Windows path that can be EXECUTED on a
// machine that is not Windows. See its header.
#[cfg(any(windows, test))]
mod winret;

use std::error::Error;
use std::{fmt, io};

#[cfg(unix)]
use self::os as primary;
#[cfg(unix)]
use self::urandom as fallback;
// Windows 10 v1809 and later: ProcessPrng, with BCryptGenRandom behind it.
#[cfg(all(windows, not(target_vendor = "win7")))]
use self::windows::bcrypt as fallback;
// The tier-3 `*-win7-windows-*` targets, where ProcessPrng does not exist and
// `std` itself falls back to the legacy pair.
#[cfg(all(windows, target_vendor = "win7"))]
use self::windows::bcrypt as primary;
#[cfg(all(windows, not(target_vendor = "win7")))]
use self::windows::process_prng as primary;
#[cfg(all(windows, target_vendor = "win7"))]
use self::windows::rtl_gen_random as fallback;

/// Every entropy source failed.
///
/// The error names each arm that was tried and why it failed, because the two
/// arms fail for genuinely different reasons — a `getentropy` failure is
/// usually a sandbox or an ancient kernel, a `/dev/urandom` failure is usually
/// a missing `/dev` or exhausted file descriptors — and the fix differs.
///
/// `Send + Sync + 'static`, so it satisfies `std::io::Error::other`, which is
/// how the `targo-trust` call sites consume it.
#[derive(Debug)]
pub struct EntropyError {
    requested: usize,
    attempts: Vec<SourceFailure>,
}

#[derive(Debug)]
struct SourceFailure {
    source: &'static str,
    error: io::Error,
}

impl EntropyError {
    /// How many bytes the failed request asked for.
    pub fn requested(&self) -> usize {
        self.requested
    }
}

impl fmt::Display for EntropyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "could not obtain {} byte(s) of operating-system entropy: every source failed",
            self.requested
        )?;
        for attempt in &self.attempts {
            write!(f, "; {}: {}", attempt.source, attempt.error)?;
        }
        // A refusal must carry the fix, with options
        // (docs/DESIGN_PHILOSOPHY.md principle 10).
        f.write_str(OPTIONS)
    }
}

/// The remedies appended to every [`EntropyError`] message.
///
/// Platform-specific because a fix that does not apply is worse than no fix: it
/// sends the reader somewhere the problem is not. Principle 10 asks a refusal to
/// carry the fix *with options*, and "mount a populated /dev" is not one of the
/// options a Windows reader has.
///
/// The closing sentence is common to both, and is the one that must never be
/// edited away: it tells a reader who is about to add a fallback that the
/// absence of bytes is the intended outcome.
#[cfg(unix)]
const OPTIONS: &str = ". Options: run outside the sandbox or seccomp filter blocking \
     getentropy(2); mount a populated /dev if this process is in a chroot or container; \
     raise the open-file limit if descriptors are exhausted. \
     No key or nonce was produced — trust-rand never substitutes a non-OS source.";

/// See [`OPTIONS`]. Every option here is a real remedy for a CNG failure: the
/// first is by far the most likely cause on a machine that boots at all, since
/// an application-directory copy or a redirection shim is loaded in preference
/// to the system DLL.
#[cfg(windows)]
const OPTIONS: &str = ". Options: check that bcryptprimitives.dll and bcrypt.dll resolve to \
     %SystemRoot%\\System32 and not to a copy beside the executable or a redirection shim; \
     check whether an AppContainer, job object or security product is blocking CNG for this \
     process; repair a damaged CNG installation (sfc /scannow); \
     if this machine predates Windows 10 version 1809, build for a *-win7-windows-* target, \
     which selects the legacy BCryptGenRandom/RtlGenRandom pair instead. \
     No key or nonce was produced — trust-rand never substitutes a non-OS source.";

impl Error for EntropyError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.attempts.last().map(|a| &a.error as &(dyn Error + 'static))
    }
}

/// Fill `dest` with operating-system entropy, or report why it was impossible.
///
/// On `Err` the contents of `dest` are **unspecified** — an arm may have
/// written a prefix before failing — and must not be used for anything. This is
/// stated rather than papered over: zeroing the buffer on failure would produce
/// a plausible-looking all-zero key, which is the exact outcome this crate is
/// built to make impossible.
///
/// An empty `dest` succeeds without contacting the operating system.
pub fn try_fill_bytes(dest: &mut [u8]) -> Result<(), EntropyError> {
    fill_with(dest, (primary::NAME, primary::fill), (fallback::NAME, fallback::fill))
}

/// The arm-composition body of [`try_fill_bytes`], with both arms injectable.
///
/// # Why the parameters exist
///
/// On every machine where this crate is tested, the primary arm succeeds. That
/// makes the fallback arm and the both-arms-failed path **unreachable from the
/// public API**, and an unreachable path is one that rots silently: deleting the
/// fallback arm outright left the whole suite green, measured. The composition
/// — try primary, try fallback only if primary failed, fail closed if both fail,
/// and name every arm that was tried in the error — is the behaviour that
/// matters here, and these parameters are what let it be *executed* in a test
/// rather than argued about. They are the same seam, and for the same reason, as
/// `urandom::fill_from_path`.
///
/// # Why this does not weaken the shipped path
///
/// The function is private; `try_fill_bytes` is its only non-test caller and
/// passes the two real arms as the sole shipped wiring. There is no feature
/// flag, no environment variable and no public entry point through which a
/// caller could substitute an arm — a build cannot select a different pair.
/// Making the arms `FnOnce` rather than a stored table also keeps the laziness
/// explicit: `fallback` is *moved into* the second `match` and is unreachable
/// when the primary succeeds, which is itself asserted by
/// `the_fallback_is_not_called_when_the_primary_succeeds`.
fn fill_with<P, F>(
    dest: &mut [u8],
    primary: (&'static str, P),
    fallback: (&'static str, F),
) -> Result<(), EntropyError>
where
    P: FnOnce(&mut [u8]) -> io::Result<()>,
    F: FnOnce(&mut [u8]) -> io::Result<()>,
{
    if dest.is_empty() {
        return Ok(());
    }
    let mut attempts = Vec::new();

    let (primary_name, fill_primary) = primary;
    match fill_primary(dest) {
        Ok(()) => return Ok(()),
        Err(error) => attempts.push(SourceFailure { source: primary_name, error }),
    }

    // The fallback rewrites the whole buffer (`read_exact`), so a partial write
    // by the arm above cannot survive into a successful result.
    let (fallback_name, fill_fallback) = fallback;
    match fill_fallback(dest) {
        Ok(()) => return Ok(()),
        Err(error) => attempts.push(SourceFailure { source: fallback_name, error }),
    }

    Err(EntropyError { requested: dest.len(), attempts })
}

/// Fill `dest` with operating-system entropy, panicking if that is impossible.
///
/// # Panics
///
/// If every entropy source fails. That is the intended behaviour: a caller that
/// wanted a nonce and cannot have one must not continue with a predictable
/// value. Use [`try_fill_bytes`] where a `Result` is wanted.
pub fn fill_bytes(dest: &mut [u8]) {
    if let Err(error) = try_fill_bytes(dest) {
        panic!("{error}");
    }
}

/// Draw a 32-byte secret seed suitable for Ed25519 key generation
/// (RFC 8032 §5.1.5), or report why it was impossible.
///
/// The seed is checked against the all-zero value before it is returned; see
/// [`is_degenerate_seed`].
pub fn try_secret_seed_32() -> Result<[u8; 32], EntropyError> {
    secret_seed_from(try_fill_bytes)
}

/// The body of [`try_secret_seed_32`], with the entropy draw injectable.
///
/// # Why the parameter exists
///
/// The tripwire in [`check_seed`] can only fire on an all-zero draw, which a
/// working entropy source never produces — so on any machine where the tests
/// run, the tripwire's *call site* is unreachable and only its predicate can be
/// exercised. That is not a hypothetical distinction: unwiring the call site
/// while leaving `is_degenerate_seed` intact left the whole suite green,
/// measured, because the existing test called the predicate directly. This
/// parameter is what makes the composition `draw -> check -> return` executable,
/// so `the_tripwire_fires_through_the_real_call_site` exercises the shipped
/// path rather than a re-implementation of it.
///
/// Private, with `try_secret_seed_32` as its only non-test caller; the public
/// API cannot supply a draw and no build configuration can disable the check.
fn secret_seed_from<F>(fill: F) -> Result<[u8; 32], EntropyError>
where
    F: FnOnce(&mut [u8]) -> Result<(), EntropyError>,
{
    let mut seed = [0u8; 32];
    fill(&mut seed)?;
    check_seed(seed)
}

/// The post-draw tripwire: reject an all-zero seed, pass anything else through
/// byte-for-byte.
///
/// Extracted from [`try_secret_seed_32`] so that the *check* and the *drawing*
/// are separately testable, and so that a test can reach the rejecting branch
/// without needing an entropy source that fails.
fn check_seed(seed: [u8; 32]) -> Result<[u8; 32], EntropyError> {
    if is_degenerate_seed(&seed) {
        return Err(EntropyError {
            requested: seed.len(),
            attempts: vec![SourceFailure {
                source: "post-draw check",
                error: io::Error::other(
                    "the entropy source returned 32 zero bytes; \
                     this is 2^-256 for a working CSPRNG and therefore a plumbing failure, \
                     not a draw",
                ),
            }],
        });
    }

    Ok(seed)
}

/// Draw a 32-byte secret seed for Ed25519 key generation, panicking if that is
/// impossible.
///
/// # Panics
///
/// If every entropy source fails, or if the source returns an all-zero seed.
pub fn secret_seed_32() -> [u8; 32] {
    match try_secret_seed_32() {
        Ok(seed) => seed,
        Err(error) => panic!("{error}"),
    }
}

/// Is this seed the all-zero value?
///
/// A tripwire, not a filter, and it is applied **only** to the 32-byte secret
/// seed. The distributional cost is exactly one excluded value out of `2^256`,
/// which no process will ever draw; the benefit is that the single most likely
/// shape of a plumbing failure — a buffer that was never written — becomes a
/// loud error instead of a key. `std` does not do this, correctly, because
/// `std`'s `fill_bytes` has no idea what the bytes are for; here we do.
///
/// It is deliberately *not* applied in [`try_fill_bytes`]: a caller asking for
/// one byte legitimately receives zero once in 256 draws.
fn is_degenerate_seed(seed: &[u8; 32]) -> bool {
    seed.iter().all(|&b| b == 0)
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use super::*;

    /// An arm that succeeds, writing a recognisable constant so that *which*
    /// arm produced the bytes is decidable rather than inferred.
    fn works(byte: u8) -> impl FnOnce(&mut [u8]) -> io::Result<()> {
        move |dest: &mut [u8]| {
            dest.fill(byte);
            Ok(())
        }
    }

    /// An arm that fails without writing.
    fn fails(kind: io::ErrorKind) -> impl FnOnce(&mut [u8]) -> io::Result<()> {
        move |_: &mut [u8]| Err(io::Error::from(kind))
    }

    // ---- GAP 1: the two-arm composition, all four combinations -------------
    //
    // On every machine this suite runs on, the primary arm succeeds. Three of
    // the four cases below are therefore unreachable through the public API,
    // which is exactly why deleting the fallback arm outright once left the
    // whole suite green. They are reached here through `fill_with`'s private
    // parameters.

    /// Case 1 of 4 — primary ok. The primary's bytes are what the caller gets,
    /// and the fallback is **not called at all**.
    #[test]
    fn a_working_primary_supplies_the_bytes_and_the_fallback_never_runs() {
        let fallback_calls = Cell::new(0u32);
        let mut buf = [0u8; 16];

        fill_with(
            &mut buf,
            ("primary", works(0x11)),
            ("fallback", |dest: &mut [u8]| {
                fallback_calls.set(fallback_calls.get() + 1);
                dest.fill(0x22);
                Ok(())
            }),
        )
        .expect("a working primary must succeed");

        assert_eq!(buf, [0x11u8; 16], "the bytes did not come from the primary arm");
        assert_eq!(
            fallback_calls.get(),
            0,
            "the fallback arm ran even though the primary succeeded; \
             the arms are being tried unconditionally rather than in order"
        );
    }

    /// Case 2 of 4 — primary fails, fallback ok. This is the entire reason the
    /// second arm exists (`ENOSYS` on a pre-3.17 Linux kernel, `EPERM` from a
    /// seccomp filter), and it had never executed.
    #[test]
    fn a_failing_primary_falls_through_to_the_fallback() {
        let mut buf = [0u8; 16];

        fill_with(
            &mut buf,
            ("primary", fails(io::ErrorKind::PermissionDenied)),
            ("fallback", works(0x22)),
        )
        .expect("a failing primary must fall through to a working fallback");

        assert_eq!(
            buf, [0x22u8; 16],
            "the fallback arm did not supply the bytes after the primary failed"
        );
    }

    /// Case 2b — the documented reason it is safe to let the fallback run over
    /// a buffer the primary already touched: `read_exact` rewrites the whole
    /// buffer, so a partial write by the failed arm cannot survive into a
    /// successful result. That sentence is in `fill_with`'s body as a comment;
    /// this is the assertion behind it.
    #[test]
    fn a_partial_write_by_a_failed_primary_does_not_survive() {
        let mut buf = [0u8; 16];

        fill_with(
            &mut buf,
            ("primary", |dest: &mut [u8]| {
                dest[..8].fill(0xDE);
                Err(io::Error::from(io::ErrorKind::Interrupted))
            }),
            ("fallback", works(0x22)),
        )
        .expect("the fallback must succeed");

        assert_eq!(
            buf, [0x22u8; 16],
            "a prefix written by the FAILED primary arm survived into the returned bytes"
        );
    }

    /// Case 3 of 4 — primary ok, fallback would fail. A broken fallback is
    /// invisible to the caller, which is the property that let the fallback rot
    /// undetected in the first place.
    #[test]
    fn a_working_primary_masks_a_broken_fallback() {
        let mut buf = [0u8; 16];

        fill_with(&mut buf, ("primary", works(0x11)), ("fallback", fails(io::ErrorKind::NotFound)))
            .expect("a broken fallback must be irrelevant while the primary works");

        assert_eq!(buf, [0x11u8; 16]);
    }

    /// Case 4 of 4 — **BOTH ARMS FAIL**. This is the crate's single most
    /// valuable claim ("there is no path on which this crate returns bytes it
    /// did not obtain from the operating system") and until now no test had
    /// ever executed it: `EntropyError` was only ever built by hand in
    /// fixtures.
    ///
    /// Asserts the three things that make the failure safe: it *is* an error,
    /// it names both arms with their distinct causes, and it leaves the
    /// destination alone rather than zeroing it into a plausible-looking key.
    #[test]
    fn when_both_arms_fail_the_result_is_fail_closed_and_names_both() {
        const SENTINEL: u8 = 0xA5;
        let mut buf = [SENTINEL; 16];

        let err = fill_with(
            &mut buf,
            ("first-arm", fails(io::ErrorKind::PermissionDenied)),
            ("second-arm", fails(io::ErrorKind::NotFound)),
        )
        .expect_err("both arms failed — this must be an error, never a silent success");

        assert_eq!(err.requested(), 16, "the error misreports the size of the failed request");
        assert_eq!(
            err.attempts.len(),
            2,
            "both arms must be recorded; only {} was/were",
            err.attempts.len()
        );
        assert_eq!(err.attempts[0].source, "first-arm", "arms recorded out of order");
        assert_eq!(err.attempts[1].source, "second-arm", "arms recorded out of order");
        assert_eq!(
            err.attempts[0].error.kind(),
            io::ErrorKind::PermissionDenied,
            "the primary arm's cause was lost"
        );
        assert_eq!(
            err.attempts[1].error.kind(),
            io::ErrorKind::NotFound,
            "the fallback arm's cause was lost"
        );

        let text = err.to_string();
        assert!(text.contains("first-arm"), "message omits the primary arm: {text}");
        assert!(text.contains("second-arm"), "message omits the fallback arm: {text}");
        assert!(text.contains("Options:"), "a refusal must carry the fix: {text}");

        // The catastrophic outcome this crate exists to prevent.
        assert!(
            buf.iter().all(|&b| b == SENTINEL),
            "a total entropy failure modified the destination buffer — a caller that \
             ignored the Err would be handed a buffer that looks written"
        );
    }

    #[test]
    fn an_empty_request_enters_neither_arm() {
        let calls = Cell::new(0u32);
        let bump = || {
            calls.set(calls.get() + 1);
            Ok(())
        };

        fill_with(&mut [], ("primary", |_: &mut [u8]| bump()), ("fallback", |_: &mut [u8]| bump()))
            .expect("an empty request must succeed");

        assert_eq!(calls.get(), 0, "an empty request entered an entropy arm");
    }

    /// The two names the shipped arms report on THIS target, pinned as
    /// literals.
    ///
    /// The names are not cosmetic: they are the only thing a fail-closed
    /// `EntropyError` tells its reader about *which* source failed, and the
    /// per-arm remedies differ. Pinning them here means a rename is a test
    /// failure rather than a silent downgrade of the error message — and it
    /// means the platform selection above is asserted, not assumed: an arm pair
    /// wired to the wrong platform's modules fails this test on the name.
    #[cfg(unix)]
    const EXPECTED_ARM_NAMES: (&str, &str) = ("getentropy(2)", "/dev/urandom");
    #[cfg(all(windows, not(target_vendor = "win7")))]
    const EXPECTED_ARM_NAMES: (&str, &str) = (
        "ProcessPrng (bcryptprimitives.dll)",
        "BCryptGenRandom (bcrypt.dll, BCRYPT_USE_SYSTEM_PREFERRED_RNG)",
    );
    #[cfg(all(windows, target_vendor = "win7"))]
    const EXPECTED_ARM_NAMES: (&str, &str) = (
        "BCryptGenRandom (bcrypt.dll, BCRYPT_USE_SYSTEM_PREFERRED_RNG)",
        "RtlGenRandom / SystemFunction036 (advapi32.dll)",
    );

    /// The shipped wiring itself. `fill_with`'s tests above prove the
    /// *composition*; this proves the composition is fed the two real arms for
    /// this platform, under the two names the fail-closed error reports.
    #[test]
    fn the_shipped_wiring_is_the_platform_arm_pair_and_both_arms_are_live() {
        assert_eq!(
            primary::NAME,
            EXPECTED_ARM_NAMES.0,
            "the primary arm's reported name changed, or the wrong module is wired as primary"
        );
        assert_eq!(
            fallback::NAME,
            EXPECTED_ARM_NAMES.1,
            "the fallback arm's reported name changed, or the wrong module is wired as fallback"
        );
        assert_ne!(primary::NAME, fallback::NAME, "both arms report the same name");

        // Each shipped arm, executed on its own. The fallback is otherwise
        // never executed on a machine where the primary works — i.e. always.
        let mut from_primary = [0u8; 64];
        primary::fill(&mut from_primary).expect("the shipped primary arm must work here");
        assert!(from_primary.iter().any(|&b| b != 0), "the shipped primary arm returned 64 zeros");

        let mut from_fallback = [0u8; 64];
        fallback::fill(&mut from_fallback).expect("the shipped fallback arm must work here");
        assert!(
            from_fallback.iter().any(|&b| b != 0),
            "the shipped fallback arm returned 64 zeros"
        );
    }

    // ---- GAP 2: the tripwire, through the real call site --------------------

    /// The tripwire fires from **the shipped seed path**, not from a direct
    /// call to the predicate.
    ///
    /// The distinction is the whole point: unwiring the call site while leaving
    /// `is_degenerate_seed` intact left the suite green, because the only test
    /// of the tripwire called the predicate itself. Here the draw is injected
    /// so that `secret_seed_from`'s own `draw -> check -> return` composition
    /// executes.
    #[test]
    fn the_tripwire_fires_through_the_real_call_site() {
        // A draw that *succeeds* and yields 32 zero bytes: the exact shape of a
        // destination that was never written.
        let err = secret_seed_from(|dest: &mut [u8]| {
            dest.fill(0);
            Ok(())
        })
        .expect_err("an all-zero draw must be rejected by the seed path itself");

        assert_eq!(err.requested(), 32);
        assert_eq!(err.attempts.len(), 1, "the tripwire's own failure record is missing");
        assert_eq!(
            err.attempts[0].source, "post-draw check",
            "the rejection did not come from the post-draw tripwire"
        );
        let text = err.to_string();
        assert!(text.contains("post-draw check"), "{text}");
        assert!(text.contains("32 zero bytes"), "{text}");
        assert!(text.contains("Options:"), "a refusal must carry the fix: {text}");
    }

    /// The other side of the tripwire, also through the real call site: a
    /// non-degenerate draw reaches the caller **unaltered**. Catches a
    /// tripwire that rejects too much, and a seed path that rewrites the bytes.
    #[test]
    fn a_non_degenerate_draw_reaches_the_caller_byte_for_byte() {
        let mut expected = [0u8; 32];
        for (i, byte) in expected.iter_mut().enumerate() {
            *byte = (i as u8).wrapping_add(1);
        }
        let seed = secret_seed_from(|dest: &mut [u8]| {
            dest.copy_from_slice(&expected);
            Ok(())
        })
        .expect("a non-degenerate seed must be accepted");
        assert_eq!(seed, expected, "the seed was altered between the draw and the caller");

        // A single set bit in the LAST byte. A tripwire that compared only a
        // prefix — the first word, say — would reject this one.
        let mut edge = [0u8; 32];
        edge[31] = 1;
        let seed = secret_seed_from(|dest: &mut [u8]| {
            dest.copy_from_slice(&edge);
            Ok(())
        })
        .expect("a seed whose only nonzero byte is the last must be accepted");
        assert_eq!(seed, edge);
    }

    /// A failed draw propagates as the *draw's* error and is not relabelled as
    /// a tripwire hit — the two failures have different fixes, so conflating
    /// them would send the reader to the wrong one. Composes both seams.
    #[test]
    fn a_failed_draw_propagates_and_is_not_reported_as_a_tripwire_hit() {
        let err = secret_seed_from(|dest: &mut [u8]| {
            fill_with(
                dest,
                ("first-arm", fails(io::ErrorKind::PermissionDenied)),
                ("second-arm", fails(io::ErrorKind::NotFound)),
            )
        })
        .expect_err("a seed must not be produced when the draw failed");

        assert_eq!(
            err.attempts.len(),
            2,
            "the seed path replaced the draw's two-arm failure record with its own"
        );
        assert_eq!(err.attempts[0].source, "first-arm");
        assert_eq!(err.attempts[1].source, "second-arm");
        assert!(
            err.attempts.iter().all(|a| a.source != "post-draw check"),
            "a draw failure was misreported as a degenerate-seed rejection"
        );
    }

    #[test]
    fn the_all_zero_seed_is_rejected() {
        assert!(is_degenerate_seed(&[0u8; 32]), "an all-zero seed must be classified degenerate");
    }

    #[test]
    fn a_seed_with_any_nonzero_byte_is_accepted() {
        // Every single-bit-set position, so an `== [0;32]` written as a partial
        // comparison (say, only the first word) is caught.
        for i in 0..32 {
            let mut seed = [0u8; 32];
            seed[i] = 1;
            assert!(
                !is_degenerate_seed(&seed),
                "a seed with byte {i} set must not be classified degenerate"
            );
        }
    }

    #[test]
    fn error_display_names_every_attempted_source_and_carries_a_fix() {
        let error = EntropyError {
            requested: 32,
            attempts: vec![
                SourceFailure {
                    source: primary::NAME,
                    error: io::Error::from(io::ErrorKind::PermissionDenied),
                },
                SourceFailure {
                    source: fallback::NAME,
                    error: io::Error::from(io::ErrorKind::NotFound),
                },
            ],
        };
        let text = error.to_string();
        assert!(text.contains("32 byte(s)"), "message omits the request size: {text}");
        assert!(text.contains(primary::NAME), "message omits the primary arm: {text}");
        assert!(text.contains(fallback::NAME), "message omits the fallback arm: {text}");
        assert!(text.contains("Options:"), "message carries no fix: {text}");
        assert_eq!(error.requested(), 32);
        assert!(error.source().is_some(), "the last failure must be reachable as a source");
    }

    /// `targo-trust`'s call sites write `.map_err(io::Error::other)?`, which
    /// requires `Send + Sync + 'static`. Pin it here so the swap does not
    /// discover it at the consumer.
    #[test]
    fn entropy_error_satisfies_io_error_other() {
        fn assert_send_sync_static<T: Send + Sync + 'static>() {}
        assert_send_sync_static::<EntropyError>();

        let error = EntropyError {
            requested: 16,
            attempts: vec![SourceFailure {
                source: primary::NAME,
                error: io::Error::from(io::ErrorKind::PermissionDenied),
            }],
        };
        let wrapped = io::Error::other(error);
        assert!(wrapped.to_string().contains(primary::NAME));
    }
}
