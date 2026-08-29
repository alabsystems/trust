// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Return-value doctrine and chunking discipline for the Windows entropy arms.
//!
//! # Why this module is compiled on non-Windows hosts under `cfg(test)`
//!
//! Everything in `crate::windows` is unexecutable on the machine this crate
//! is developed on, and the crate's rigor bar is that a test which has never
//! been *seen to fail* is not evidence. The parts of the Windows arms that can
//! be wrong in an interesting way are not the FFI calls — those are four lines
//! each — but the two decisions wrapped around them:
//!
//! 1. **Which return values mean "the buffer was filled".** Getting this wrong
//!    in the permissive direction hands back an unwritten buffer, which for a
//!    freshly zeroed seed is a zero key. This is the exact hazard
//!    `crate::os` documents for the raw-syscall carry-flag convention.
//! 2. **Whether a request larger than one call is covered end to end.** Two of
//!    the three Windows entries take a `ULONG` length, so a naive
//!    `len as u32` truncates a large request silently.
//!
//! Both are pure integer/slice logic with no ABI content, so they are hoisted
//! here, given `#[cfg(any(<their platform>, test))]`, and tested on whatever
//! host runs `cargo test`. **These are the real functions the Windows arms
//! call, not a replica** — same items, same source, differing only in target
//! triple, which for `i32`/`u8`/`usize` arithmetic changes nothing.
//!
//! What this does **not** establish: that the declared signatures match the
//! real Windows ABI, that the DLLs export what we name, or that any of it runs.
//! That evidence is compile-only and is stated as such in `crate::windows`.
//!
//! # The uniform rule: accept exactly the documented success value
//!
//! All three Windows entries document a single success value, and each of the
//! three classifiers below tests for *that value* rather than for the absence
//! of an obvious failure marker. The reasoning is `crate::os`'s, transposed:
//! `ret != 0`, `status >= 0` and friends are the shapes that let an
//! undocumented return be read as success.
//!
//! The cost of the strict direction is bounded and is a liveness cost, never a
//! secrecy one: a spuriously rejected success falls through to the next arm, or
//! — on the last arm — panics. A spuriously *accepted* failure returns an
//! unwritten buffer as a key. Those are not symmetric, so the rule leans the
//! way it does.

use std::io;

/// `TRUE`, as `library/std/src/sys/pal/windows/c/windows_sys.rs:3368` defines
/// it: `pub const TRUE: BOOL = 1i32;`.
#[cfg(any(all(windows, not(target_vendor = "win7")), test))]
pub(crate) const TRUE: i32 = 1;

/// `STATUS_SUCCESS`, from `ntstatus.h`: `((NTSTATUS)0x00000000L)`.
#[cfg(any(windows, test))]
pub(crate) const STATUS_SUCCESS: i32 = 0;

/// `BOOLEAN`'s `TRUE`, from `ntdef.h`: `#define TRUE 1`. `BOOLEAN` is
/// `unsigned char`, not `BOOL`.
#[cfg(any(all(windows, target_vendor = "win7"), test))]
pub(crate) const BOOLEAN_TRUE: u8 = 1;

/// Classify a `BOOL` return whose documented success value is `TRUE`.
///
/// Used by the `ProcessPrng` arm. Microsoft's reference page for that function
/// states its return value in full as *"ProcessPrng returns TRUE."* — there is
/// no documented failure value and no documented error channel, so a return of
/// anything else is a contract violation with no defined meaning, and the only
/// safe reading of it is "this call did not do what it says".
///
/// `std` agrees on the expected value: `library/std/src/sys/random/windows.rs`
/// asserts `debug_assert_eq!(ret, c::TRUE)`. The difference here is that this
/// crate must hold in release builds too, and must *route* rather than assert.
///
/// The error is built with [`io::Error::other`] rather than
/// [`io::Error::last_os_error`] on purpose: `ProcessPrng` is not documented to
/// set the thread's last-error value, so `last_os_error()` would report an
/// unrelated stale code from some earlier call and send a reader chasing it.
#[cfg(any(all(windows, not(target_vendor = "win7")), test))]
pub(crate) fn bool_is_true(name: &str, ret: i32) -> io::Result<()> {
    if ret == TRUE {
        Ok(())
    } else {
        Err(io::Error::other(format!(
            "{name} returned {ret}, and its documented return value is TRUE ({TRUE}); \
             the destination buffer must be treated as unwritten"
        )))
    }
}

/// Classify an `NTSTATUS` return whose documented success value is
/// `STATUS_SUCCESS`.
///
/// Used by the `BCryptGenRandom` arm. Two traps are closed here:
///
/// * **`NTSTATUS` is not a Win32 error code and `BCryptGenRandom` does not set
///   the thread's last-error value.** `io::Error::last_os_error()` would
///   therefore report something unrelated. The status is formatted into the
///   message instead, as an unsigned hex word, which is how every Microsoft
///   table lists these codes.
/// * **`status >= 0` is the wrong test.** The `NTSTATUS` severity field makes
///   `0x4xxxxxxx` (informational) and `0x8xxxxxxx` (warning) non-negative and
///   negative respectively, so a sign test both accepts informational codes and
///   is easy to write backwards. `STATUS_SUCCESS` is the only documented
///   outcome in which `pbBuffer` is filled.
#[cfg(any(windows, test))]
pub(crate) fn ntstatus_is_success(name: &str, status: i32) -> io::Result<()> {
    if status == STATUS_SUCCESS {
        Ok(())
    } else {
        Err(io::Error::other(format!(
            "{name} returned NTSTATUS 0x{:08X}, not STATUS_SUCCESS (0x00000000); \
             the destination buffer must be treated as unwritten",
            status as u32
        )))
    }
}

/// Classify a `BOOLEAN` return whose documented success value is `TRUE`.
///
/// Used by the legacy `RtlGenRandom` arm. Unlike the two above, this entry
/// *is* documented to set the thread's last-error value on failure — *"To get
/// extended error information, call GetLastError"* — so the rendered
/// `last_os_error()` is included, as context inside the message rather than as
/// the error itself, so that the "which value came back" fact is never lost.
///
/// The `windows-sys` binding vendored into `std`
/// (`library/std/src/sys/pal/windows/c/windows_sys.rs:93`) declares this
/// return as a Rust `bool`, which is only sound if the callee returns exactly
/// `0` or `1`; testing for `1` here is therefore no stricter than the
/// assumption `std` already ships, and it is checked rather than assumed.
#[cfg(any(all(windows, target_vendor = "win7"), test))]
pub(crate) fn boolean_is_true(name: &str, ret: u8) -> io::Result<()> {
    if ret == BOOLEAN_TRUE {
        Ok(())
    } else {
        let last = io::Error::last_os_error();
        Err(io::Error::other(format!(
            "{name} returned {ret}, and its documented return value is TRUE ({BOOLEAN_TRUE}); \
             the destination buffer must be treated as unwritten (GetLastError: {last})"
        )))
    }
}

/// Split `dest` into `max_per_call`-sized pieces and hand each to `call`,
/// stopping at the first error.
///
/// This is the discipline `crate::os::fill` applies for `getentropy`'s
/// documented 256-byte cap, restated for the Windows entries whose length
/// parameter is a `ULONG`. It is a separate function rather than an open-coded
/// loop in each arm because it is the only part of those arms that can be
/// tested on this machine.
///
/// On error the contents of `dest` are unspecified: a prefix may have been
/// written. Callers reach this through the crate's fail-closed composition,
/// which either overwrites the whole buffer from another arm or reports
/// failure — it never returns a partly-written buffer as a success.
#[cfg(any(windows, test))]
pub(crate) fn fill_in_chunks(
    dest: &mut [u8],
    max_per_call: usize,
    mut call: impl FnMut(&mut [u8]) -> io::Result<()>,
) -> io::Result<()> {
    // `chunks_mut(0)` panics; a zero here would be a caller bug, and the
    // assertion names it rather than letting the panic point at libcore.
    assert!(max_per_call > 0, "a chunk size of zero cannot make progress");

    if dest.is_empty() {
        // Same reasoning as the empty-request short circuit in `crate::os`:
        // a zero-length request has no reason to cross the FFI boundary, and
        // skipping it means an empty slice's dangling-but-aligned pointer is
        // never handed to a foreign function.
        return Ok(());
    }

    for chunk in dest.chunks_mut(max_per_call) {
        call(chunk)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;

    // ---- return-value classification --------------------------------------

    #[test]
    fn a_bool_of_exactly_true_is_success() {
        bool_is_true("probe", TRUE).expect("TRUE is the documented success value");
    }

    #[test]
    fn a_bool_of_false_is_a_failure() {
        let err = bool_is_true("probe", 0).expect_err("FALSE must be reported as a failure");
        let text = err.to_string();
        assert!(text.contains("probe"), "the message must name the arm: {text}");
        assert!(text.contains("unwritten"), "the message must say the buffer is unusable: {text}");
    }

    /// The mutation this test exists to catch is `ret == TRUE` weakened to
    /// `ret != 0`. Under that weakening an undocumented non-zero return — which
    /// carries no promise that `pbData` was written — is read as success.
    #[test]
    fn a_bool_that_is_neither_true_nor_false_is_a_failure() {
        for ret in [2i32, -1, i32::MIN, i32::MAX, 0x1000] {
            let err = match bool_is_true("probe", ret) {
                Ok(()) => panic!(
                    "bool_is_true accepted {ret} as success; only the documented TRUE ({TRUE}) \
                     carries a promise that the buffer was written"
                ),
                Err(error) => error,
            };
            assert!(
                err.to_string().contains(&format!("returned {ret}")),
                "the message must carry the actual return value: {err}"
            );
        }
    }

    #[test]
    fn an_ntstatus_of_status_success_is_success() {
        ntstatus_is_success("probe", STATUS_SUCCESS).expect("0 is STATUS_SUCCESS");
    }

    /// Catches `status == STATUS_SUCCESS` weakened to `status >= 0`. The two
    /// non-negative values below are real `NTSTATUS` severity classes:
    /// `0x00000001` is `STATUS_WAIT_1` and `0x40000000` has the informational
    /// severity bit set. Neither means `pbBuffer` was filled.
    #[test]
    fn a_non_negative_ntstatus_that_is_not_zero_is_still_a_failure() {
        for status in [1i32, 0x4000_0000, i32::MAX] {
            let err = ntstatus_is_success("probe", status)
                .expect_err("only STATUS_SUCCESS may be read as success");
            assert!(
                err.to_string().contains(&format!("0x{:08X}", status as u32)),
                "the message must carry the actual status: {err}"
            );
        }
    }

    /// The ordinary failure direction: a negative (error-severity) status.
    /// `0xC0000001` is `STATUS_UNSUCCESSFUL`.
    #[test]
    fn a_negative_ntstatus_is_a_failure() {
        let err = ntstatus_is_success("probe", 0xC000_0001u32 as i32)
            .expect_err("an error-severity NTSTATUS must fail");
        let text = err.to_string();
        assert!(text.contains("0xC0000001"), "status not rendered unsigned: {text}");
        assert!(text.contains("probe"), "the message must name the arm: {text}");
    }

    #[test]
    fn a_boolean_of_exactly_true_is_success() {
        boolean_is_true("probe", BOOLEAN_TRUE).expect("1 is the documented success value");
    }

    /// Catches `ret == BOOLEAN_TRUE` weakened to `ret != 0`, and pins the
    /// FALSE case.
    #[test]
    fn a_boolean_that_is_not_exactly_true_is_a_failure() {
        for ret in [0u8, 2, 0xFF] {
            let err = boolean_is_true("probe", ret)
                .expect_err("only the documented TRUE may be read as success");
            assert!(
                err.to_string().contains("unwritten"),
                "the message must say the buffer is unusable: {err}"
            );
        }
    }

    // ---- chunking ---------------------------------------------------------

    /// Records the length of every chunk it is handed and fills it with a
    /// per-chunk marker, so that both the split and the coverage can be
    /// checked afterwards.
    fn recording_call<'a>(
        log: &'a RefCell<Vec<usize>>,
    ) -> impl FnMut(&mut [u8]) -> io::Result<()> + 'a {
        move |chunk: &mut [u8]| {
            let index = log.borrow().len();
            log.borrow_mut().push(chunk.len());
            chunk.fill(u8::try_from(index % 251).unwrap().wrapping_add(1));
            Ok(())
        }
    }

    #[test]
    fn every_byte_is_covered_exactly_once_including_the_partial_tail() {
        const MAX: usize = 7;
        for len in [1usize, 6, 7, 8, 13, 14, 15, 100] {
            let log = RefCell::new(Vec::new());
            let mut buf = vec![0u8; len];
            fill_in_chunks(&mut buf, MAX, recording_call(&log)).expect("the fake call cannot fail");

            let sizes = log.into_inner();
            assert_eq!(
                sizes.iter().sum::<usize>(),
                len,
                "len={len}: chunk sizes {sizes:?} do not sum to the request"
            );
            assert!(
                sizes.iter().all(|&n| n > 0 && n <= MAX),
                "len={len}: a chunk exceeded the per-call limit: {sizes:?}"
            );
            assert_eq!(
                sizes.len(),
                len.div_ceil(MAX),
                "len={len}: wrong number of calls: {sizes:?}"
            );
            // Every byte was written by some chunk: the marker is never zero.
            assert!(
                buf.iter().all(|&b| b != 0),
                "len={len}: some byte was never handed to the call"
            );
        }
    }

    /// The mutation this catches is a loop that drops the final partial chunk
    /// (`chunks_mut` -> `chunks_exact_mut`). At `len = 10, MAX = 4` that leaves
    /// the last two bytes at their sentinel.
    #[test]
    fn the_final_partial_chunk_is_not_dropped() {
        let log = RefCell::new(Vec::new());
        let mut buf = vec![0u8; 10];
        fill_in_chunks(&mut buf, 4, recording_call(&log)).expect("the fake call cannot fail");
        assert_eq!(log.into_inner(), vec![4, 4, 2], "the trailing 2-byte chunk was not issued");
        assert!(buf.iter().all(|&b| b != 0), "the trailing bytes were never written");
    }

    /// A request smaller than one call must still be issued whole, and must not
    /// be padded up to the limit.
    #[test]
    fn a_request_below_the_limit_is_one_call_of_exactly_that_size() {
        let log = RefCell::new(Vec::new());
        let mut buf = vec![0u8; 3];
        fill_in_chunks(&mut buf, 4096, recording_call(&log)).expect("the fake call cannot fail");
        assert_eq!(log.into_inner(), vec![3]);
    }

    #[test]
    fn an_empty_request_never_reaches_the_call() {
        let log = RefCell::new(Vec::new());
        fill_in_chunks(&mut [], 4096, recording_call(&log))
            .expect("an empty request must succeed without a call");
        assert!(log.into_inner().is_empty(), "the FFI boundary was crossed for zero bytes");
    }

    /// A failure part-way through must propagate and must not keep calling. The
    /// mutation this catches is `call(chunk)?` weakened to `let _ = call(chunk);`,
    /// which would report success for a buffer whose tail was never written.
    #[test]
    fn the_first_error_stops_the_loop_and_propagates() {
        let calls = RefCell::new(0usize);
        let result = fill_in_chunks(&mut [0u8; 100], 10, |_chunk| {
            *calls.borrow_mut() += 1;
            if *calls.borrow() == 3 {
                Err(io::Error::other("synthetic arm failure"))
            } else {
                Ok(())
            }
        });

        let err = result.expect_err("an arm failure must not be swallowed");
        assert!(err.to_string().contains("synthetic arm failure"), "wrong error: {err}");
        assert_eq!(calls.into_inner(), 3, "the loop kept going after a failure");
    }

    #[test]
    #[should_panic(expected = "chunk size of zero")]
    fn a_zero_chunk_size_is_a_loud_caller_bug() {
        let _ = fill_in_chunks(&mut [0u8; 4], 0, |_| Ok(()));
    }
}
