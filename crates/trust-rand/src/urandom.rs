// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The fallback entropy arm: **`/dev/urandom`**.
//!
//! # Why there is a second arm at all
//!
//! `crate::os` can fail at runtime for reasons that are not "the machine has
//! no entropy": a Linux kernel older than 3.17 has no `getrandom` syscall and
//! glibc's `getentropy` returns `ENOSYS`; a seccomp filter can block it with
//! `EPERM`. In both cases the character device still works. Trying it costs one
//! `open` on a path that is already failing, and turns a hard failure into a
//! degraded-but-correct one.
//!
//! # Why it is the FALLBACK and not the primary
//!
//! It is strictly weaker than `getentropy` on four independent axes, and each
//! one is a real failure mode rather than a theoretical one:
//!
//! 1. **No early-boot guarantee on Linux.** `/dev/urandom` always yields bytes,
//!    including before the CSPRNG pool is initialized. That is precisely why
//!    `std`'s own Linux backend polls `/dev/random` for readiness *before*
//!    reading `/dev/urandom` when it wants secure data
//!    (`library/std/src/sys/random/linux.rs`). This crate does not replicate
//!    that poll, because the arm that has the property natively is tried first.
//! 2. **It needs a path.** Fails inside a chroot or mount namespace with no
//!    populated `/dev`.
//! 3. **It needs a file descriptor.** Fails under fd exhaustion — a state a
//!    long-running build tool can genuinely reach.
//! 4. **Short reads become the caller's correctness burden.** A partial read
//!    that is treated as success leaves the tail of the buffer at whatever it
//!    was, which for a freshly zeroed seed is zeros. This module uses
//!    [`Read::read_exact`], whose contract is all-or-error, and the test
//!    `short_read_is_an_error_not_a_silent_partial_fill` pins that by reading
//!    from `/dev/null`.
//!
//! # What it guarantees
//!
//! On every Unix this crate supports, `/dev/urandom` is a kernel CSPRNG. Once
//! the pool is initialized its output is cryptographically secure and
//! unlimited. The one property it does not carry is *when* that initialization
//! happened relative to this read.

use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

/// Human-readable name of this arm, used in [`crate::EntropyError`]'s message.
pub(crate) const NAME: &str = "/dev/urandom";

/// The device this arm reads.
const DEVICE: &str = "/dev/urandom";

/// Fill `dest` entirely from `/dev/urandom`, or return an error.
pub(crate) fn fill(dest: &mut [u8]) -> io::Result<()> {
    fill_from_path(Path::new(DEVICE), dest)
}

/// The path-parameterised body of [`fill`].
///
/// The parameter exists for one reason: it is the seam that lets the failure
/// path be *exercised* rather than argued about. `/dev/null` produces a
/// zero-length read (the silent-partial-fill hazard) and a nonexistent path
/// produces `NotFound` (the no-`/dev` hazard); both are asserted below.
pub(crate) fn fill_from_path(path: &Path, dest: &mut [u8]) -> io::Result<()> {
    if dest.is_empty() {
        return Ok(());
    }
    let mut device = File::open(path)?;
    // `read_exact` is all-or-error: on a short read it returns
    // `ErrorKind::UnexpectedEof` rather than reporting how much it managed.
    // A plain `read` here would be the defect this whole crate is about.
    device.read_exact(dest)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_real_device_fills_the_whole_buffer() {
        let mut buf = [0u8; 512];
        fill(&mut buf).expect("/dev/urandom must be readable in the test environment");
        assert!(buf.iter().any(|&b| b != 0), "512 bytes from /dev/urandom were all zero");
        // Both halves, so a "fills only the first read's worth" defect shows up.
        assert!(buf[..256].iter().any(|&b| b != 0), "first half was left zero");
        assert!(buf[256..].iter().any(|&b| b != 0), "second half was left zero");
    }

    /// THE failure this arm is most likely to get wrong. `/dev/null` returns
    /// `Ok(0)` from `read`, i.e. end-of-file. An implementation that used
    /// `read` and ignored the count would report success and hand back the
    /// buffer exactly as it found it — all zeros for a fresh seed.
    ///
    /// Establishes: a short read is reported as an error, and the buffer is
    /// left at its sentinel rather than being passed off as entropy.
    #[test]
    fn short_read_is_an_error_not_a_silent_partial_fill() {
        let mut buf = [0xAAu8; 64];
        let err = fill_from_path(Path::new("/dev/null"), &mut buf)
            .expect_err("reading 64 bytes from /dev/null must fail, not silently succeed");
        assert_eq!(
            err.kind(),
            io::ErrorKind::UnexpectedEof,
            "expected an end-of-file error from /dev/null, got: {err}"
        );
        assert!(buf.iter().all(|&b| b == 0xAA), "the failed read modified the destination buffer");
    }

    /// The no-`/dev` case (chroot, minimal container, mount namespace).
    #[test]
    fn a_missing_device_is_an_error() {
        let mut buf = [0xAAu8; 32];
        let err =
            fill_from_path(Path::new("/nonexistent/trust-rand/no-such-entropy-device"), &mut buf)
                .expect_err("a nonexistent device path must fail");
        assert_eq!(err.kind(), io::ErrorKind::NotFound, "unexpected error kind: {err}");
        assert!(buf.iter().all(|&b| b == 0xAA), "the failed open modified the destination buffer");
    }

    #[test]
    fn an_empty_request_does_not_even_open_the_device() {
        // A nonexistent path would fail if the device were opened.
        fill_from_path(Path::new("/nonexistent/trust-rand/no-such-entropy-device"), &mut [])
            .expect("an empty request must succeed without touching the filesystem");
    }
}
