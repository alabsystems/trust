// Authoritative completeness: a project's own `unsafe fn` with a name Trust's
// heuristic does NOT list, and which Trust does not model, must still be CAUGHT
// fail-closed at the call site — driven by rustc's `fn_sig().safety()`, so no
// unsafe call silently escapes ("prove no others exist").
//   trustc -Z trust-verify-output=human --crate-type lib unmodeled_unsafe_call_caught.rs
#![allow(dead_code)]

/// An unsafe fn with an arbitrary name — not in any Trust name list, not modeled.
pub unsafe fn frobnicate_raw(x: u64) -> u64 {
    x ^ 0xDEAD_BEEF
}

/// Calling it requires `unsafe`; the call must be CAUGHT (`[unsafe:unmodeled-call]`).
pub fn caller(x: u64) -> u64 {
    unsafe { frobnicate_raw(x) }
}

/// Control: a SAFE call must NOT be flagged.
pub fn safe_caller(x: u64) -> u64 {
    x.wrapping_add(1)
}
