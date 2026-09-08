//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! §5 STEP 5 (`GlobalAlloc::dealloc` caller contract), fixture (c) — THE
//! SLICE'S DOCUMENTED STOPPING POINT. Plan of record:
//! docs/design/2026-08-19-verified-sysroot-scoping.md §5 step 5.
//!
//! A user `#[global_allocator]` whose `dealloc` is trivially PANIC-FREE (an
//! empty body — it verifies clean on its own, no error lands on it below).
//! The plan's full machinery would DISCHARGE the contract at this impl. The
//! slice landed first does not implement the discharge-at-impl lane, so the
//! contract still REFUSES — fail-CLOSED, never assumed: the "caller contract
//! is refused" error on `drops_vec` is this file's pin.
//!
//! WHEN THE DISCHARGE-AT-IMPL LANE LANDS this file must flip: the refusal
//! error disappears (the contract discharges at the verified panic-free
//! `dealloc`), while the panicking sibling
//! `..._panicking_user_dealloc_refused.rs` MUST keep refusing. Keeping this
//! pair green through that flip is the acceptance test for the lane.
//!
//! The remaining annotations are the MEASURED pre-existing baseline (stage1
//! trustc, 2026-08-30): the four `#[global_allocator]`-expanded `__rust_*`
//! shim bodies fail strict verification today (8 errors on the registration
//! static's line), and `drops_vec` keeps its pre-existing strict failure (the
//! `Vec` drop-glue classifier gap, not this file's subject).
use std::alloc::{GlobalAlloc, Layout};

pub struct QuietAlloc;

unsafe impl GlobalAlloc for QuietAlloc {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        core::ptr::null_mut()
    }
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

#[global_allocator]
pub static A: QuietAlloc = QuietAlloc;
//~^ ERROR Trust Level 0 safety verification incomplete
//~| ERROR Trust strict verification failed
//~| ERROR Trust Level 0 safety verification incomplete
//~| ERROR Trust strict verification failed
//~| ERROR Trust Level 0 safety verification incomplete
//~| ERROR Trust strict verification failed
//~| ERROR Trust Level 0 safety verification incomplete
//~| ERROR Trust strict verification failed

pub fn drops_vec(v: Vec<u8>) -> usize {
    // RE-PINNED on the composed build. This fn line carries THREE diagnostics:
    // the L0 header (WARN), the contract refusal, and the obligation-count
    // strict error. Two strict ERRORs share the line and compiletest pairs
    // same-line same-kind annotations POSITIONALLY, so both carry mutually
    // exclusive substrings. Annotations sit directly under the fn line: one
    // caret, no arithmetic.
    //~^^^^^^^ WARN Trust Level 0 safety verification incomplete
    //~| ERROR the `contract:global-alloc-dealloc-panic-free`
    //~| ERROR 1 obligation(s) were not fully verified
    v.len()
}
