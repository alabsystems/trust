// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The primary entropy arm: **`getentropy(2)`**.
//!
//! # What this is, and what it deliberately is not
//!
//! This is a call to the C library function `getentropy`, declared here rather
//! than imported from the `libc` crate — a declaration is not a dependency, and
//! the symbol is in `libSystem` / `libc`, which every Rust program on these
//! platforms already links.
//!
//! It is **not** a raw syscall, and the distinction is load-bearing. A raw
//! `svc #0x80` with `x16 = 500` reaches the same kernel service on
//! aarch64-apple-darwin, but macOS BSD syscalls report failure in the **carry
//! flag** while leaving a *positive* errno in `x0`. A Linux-idiomatic
//! `if ret < 0` check therefore reads a failed 1024-byte request as success and
//! hands back a zero-filled buffer — measured, in this tree, on this machine:
//!
//! ```text
//! // raw svc, 1024-byte request (getentropy caps at 256)
//! ret(x0) = 22   carry(error flag) = 1
//! first 32 bytes = [00, 00, ... 00]     all-zero? true
//! ```
//!
//! The libc wrapper has no such trap: it returns `0` on success and `-1` on
//! failure with `errno` set, which is what [`getentropy_chunk`] checks. Apple
//! also does not treat syscall numbers as a stable ABI — `libSystem` is the
//! supported boundary — so going through the wrapper is both safer and more
//! durable.
//!
//! # What it guarantees, per platform
//!
//! `getentropy` is specified to return **cryptographically secure** bytes or
//! fail; there is no "best effort" mode and no partial success. Concretely:
//!
//! | Platform | Backing | Since |
//! |---|---|---|
//! | macOS / iOS | kernel CSPRNG, direct syscall (`SYS_getentropy`, 500) | 10.12 |
//! | Linux (glibc) | `getrandom(buf, len, 0)` — **blocks until the entropy pool is initialized** | glibc 2.25 |
//! | Linux (musl) | `getrandom` syscall, same blocking semantics | musl 1.1.20 |
//! | OpenBSD | native, the origin of the interface | 5.6 |
//! | FreeBSD / NetBSD / Solaris | native, kernel CSPRNG | FreeBSD 12, NetBSD 8, Solaris 11.3 |
//!
//! Two properties matter here and are the reason this arm outranks a bare
//! `/dev/urandom` read:
//!
//! * **Correct at process start.** On Linux the flags-`0` `getrandom` path
//!   blocks until the non-blocking pool is initialized. A direct
//!   `/dev/urandom` read does not — it always yields bytes, initialized or not.
//! * **No file descriptor.** It works inside a chroot or mount namespace with
//!   no `/dev`, and under file-descriptor exhaustion. Both are real failure
//!   modes for the fallback arm.
//!
//! A third property, worth stating because it is the classic hazard for the
//! *other* obvious choice: there is **no userspace CSPRNG state**, so there is
//! no duplicate-stream-after-`fork()` hazard. `arc4random_buf` and
//! `CCRandomGenerateBytes` (which is what `std`'s own `SystemRng` uses on
//! Apple) maintain a thread-local userspace generator and depend on
//! `pthread_atfork` handlers to reseed; `getentropy` enters the kernel on every
//! call and cannot duplicate.
//!
//! That last paragraph is an argument, so it was also **measured** rather than
//! left as one — a parent that draws once *before* forking (which is what makes
//! a userspace generator duplicate), then parent and child each draw again,
//! through `libSystem`'s `fork()` so `pthread_atfork` handlers run as they
//! would in a real program. Three runs on aarch64-apple-darwin:
//!
//! ```text
//! parent post-fork = [27, 62, a0, d1, ...]   child = [bd, 58, 77, 13, ...]   DUPLICATED: false
//! parent post-fork = [b1, e3, 9b, 40, ...]   child = [0f, f6, e7, cc, ...]   DUPLICATED: false
//! parent post-fork = [19, 9b, 15, d4, ...]   child = [93, b8, 1c, 64, ...]   DUPLICATED: false
//! ```
//!
//! The probe is deliberately NOT in this crate's test suite: `fork()` inside a
//! threaded libtest harness is a flakiness source, and the property being
//! checked is a property of the kernel interface, not of code that can regress
//! here.
//!
//! # Availability is a LINK-time question, not a runtime one
//!
//! If the symbol is absent the program fails to link — loudly, at build time.
//! It cannot degrade into weak bytes. The runtime fallback in
//! `crate::urandom` exists for the *other* failure: a kernel too old to
//! implement the call (`ENOSYS` on Linux < 3.17), or a seccomp filter blocking
//! it.

use core::ffi::{c_int, c_void};
use std::io;

/// Human-readable name of this arm, used in [`crate::EntropyError`]'s message.
pub(crate) const NAME: &str = "getentropy(2)";

/// The maximum number of bytes `getentropy` will produce in one call.
///
/// This is not a tuning parameter. It is specified — OpenBSD `getentropy(2)`,
/// the Linux `getentropy(3)` man page and Apple's `getentropy(2)` all state a
/// hard limit of 256 bytes, and a larger request fails with `EIO` (BSD) or
/// `EINVAL` (Linux/Apple) **without writing anything**. Measured here on
/// aarch64-apple-darwin, a 300-byte request returned `-1` /
/// `Invalid argument (os error 22)` and left the buffer entirely zero — which
/// is exactly the shape of the catastrophic failure this crate exists to
/// prevent, and exactly why [`fill`] chunks and why [`getentropy_chunk`]
/// checks the return value.
const MAX_PER_CALL: usize = 256;

// The C declaration. Not a dependency: `getentropy` lives in libSystem on
// Apple platforms and in libc elsewhere, both of which are already linked into
// every Rust binary on those targets.
//
// Signature, from the man page:  int getentropy(void *buf, size_t buflen);
// `c_int` is i32 and `size_t` is `usize` on every target this crate supports.
unsafe extern "C" {
    fn getentropy(buf: *mut c_void, buflen: usize) -> c_int;
}

/// One `getentropy` call, filling **all** of `dest` or returning an error.
///
/// `dest` must be no longer than [`MAX_PER_CALL`]; a longer slice is rejected
/// by the OS and reported as an error rather than silently truncated. This
/// function is `pub(crate)` rather than private so that the chunking discipline
/// in [`fill`] can be shown to be load-bearing — see `tests::oversize_single_call_is_rejected`.
pub(crate) fn getentropy_chunk(dest: &mut [u8]) -> io::Result<()> {
    if dest.is_empty() {
        // A zero-length request is well-defined (`getentropy` returns 0), but
        // there is no reason to enter the kernel for it, and skipping the call
        // means an empty slice's dangling-but-aligned pointer is never handed
        // across the FFI boundary.
        return Ok(());
    }

    // SAFETY: `dest.as_mut_ptr()` is valid for writes of `dest.len()` bytes
    // (that is the definition of a `&mut [u8]`), `u8` has no alignment
    // requirement beyond 1, and `getentropy` writes exactly `buflen` bytes on
    // success and none on failure. The pointer is not retained by the callee.
    let ret = unsafe { getentropy(dest.as_mut_ptr().cast::<c_void>(), dest.len()) };

    // The libc contract is `0` or `-1`; anything else is a broken libc. Test
    // for the success value rather than for `ret < 0`, so that a hypothetical
    // positive-errno convention (the raw-syscall trap documented in the module
    // header) is still classified as a failure.
    if ret == 0 { Ok(()) } else { Err(io::Error::last_os_error()) }
}

/// Fill `dest` entirely from `getentropy`, in [`MAX_PER_CALL`]-byte chunks.
///
/// On error the contents of `dest` are unspecified — some prefix may have been
/// written — and must not be used. Callers reach this through
/// [`crate::try_fill_bytes`], which either overwrites the whole buffer from the
/// fallback arm or reports failure.
pub(crate) fn fill(dest: &mut [u8]) -> io::Result<()> {
    for chunk in dest.chunks_mut(MAX_PER_CALL) {
        getentropy_chunk(chunk)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The chunking in [`fill`] is not decoration. Requesting more than
    /// [`MAX_PER_CALL`] in a single call **fails**, and — this is the part that
    /// matters — fails while leaving the buffer untouched, i.e. all zero.
    ///
    /// Establishes: the return-value check in [`getentropy_chunk`] catches the
    /// exact case that would otherwise produce a zero-filled "random" buffer.
    #[test]
    fn oversize_single_call_is_rejected() {
        let mut buf = [0u8; MAX_PER_CALL + 1];
        let err = getentropy_chunk(&mut buf)
            .expect_err("getentropy must reject a request larger than 256 bytes");
        // Do not pin the errno: BSD says EIO, Linux/Apple say EINVAL. What is
        // being pinned is that it is reported as an error at all.
        assert!(
            buf.iter().all(|&b| b == 0),
            "the OS wrote into the buffer on a failed call; \
             this test's premise (a failed call yields zeros) no longer holds: {err}"
        );
    }

    /// A request at exactly the documented limit must succeed. This pins the
    /// constant from the other side: if [`MAX_PER_CALL`] were raised, the test
    /// above would still pass (a bigger number is still rejected) but this one
    /// would fail.
    #[test]
    fn a_full_size_single_call_succeeds() {
        let mut buf = [0u8; MAX_PER_CALL];
        getentropy_chunk(&mut buf).expect("a 256-byte request is within the documented limit");
        assert!(buf.iter().any(|&b| b != 0), "256 bytes of entropy were all zero");
    }

    /// A draw far larger than one call fills the whole buffer, including the
    /// final partial chunk. Catches both "loop only runs once" and "loop drops
    /// the remainder" mutations.
    #[test]
    fn a_large_draw_is_filled_all_the_way_to_the_end() {
        // 4096 + 37: sixteen full chunks and a partial one.
        let mut buf = vec![0u8; MAX_PER_CALL * 16 + 37];
        fill(&mut buf).expect("getentropy must satisfy a chunked request");

        // Every chunk-sized window must contain a nonzero byte. For a working
        // CSPRNG the probability of a false failure is 2^-2048 per window.
        for (i, window) in buf.chunks(MAX_PER_CALL).enumerate() {
            assert!(
                window.iter().any(|&b| b != 0),
                "window {i} ({} bytes, offset {}) was left entirely zero — the chunk loop \
                 did not cover the whole buffer",
                window.len(),
                i * MAX_PER_CALL
            );
        }
        // The trailing partial chunk specifically.
        let tail = &buf[MAX_PER_CALL * 16..];
        assert_eq!(tail.len(), 37);
        assert!(tail.iter().any(|&b| b != 0), "the final partial chunk was left zero");
    }

    #[test]
    fn an_empty_request_is_a_no_op() {
        fill(&mut []).expect("an empty request must succeed without entering the kernel");
        getentropy_chunk(&mut []).expect("an empty chunk must succeed");
    }
}
