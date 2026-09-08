//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! §5 STEP 5 (`GlobalAlloc::dealloc` caller contract), fixture (b) — THE
//! ENTIRE POINT of the step. Plan of record:
//! docs/design/2026-08-19-verified-sysroot-scoping.md §5 step 5.
//!
//! A user `#[global_allocator]` whose `dealloc` PANICS. Before this step,
//! "dealloc is total" was a silent axiom of the bridge's
//! `is_std_owning_or_scaffold` allowlist: any drop discharge that leaned on it
//! simply assumed a panicking dealloc away. Now the premise is the published
//! `contract:global-alloc-dealloc-panic-free` row, and with a user allocator
//! registered it must REFUSE — the load-bearing annotation below is the
//! distinctive "caller contract is refused" error on `drops_vec`, the body
//! charged for its allocation-owning `Vec<u8>` drop.
//!
//! Everything else this crate emits is the MEASURED pre-existing baseline
//! (stage1 trustc, 2026-08-30), annotated so a drift is loud:
//! * the panicking `dealloc` impl fails its own verification (2 errors);
//! * the four `#[global_allocator]`-expanded `__rust_*` shim bodies each fail
//!   strict verification today (8 errors on the registration static's line);
//! * `drops_vec` keeps its pre-existing strict failure (the `Vec` drop glue
//!   still declines the structural classifier — the
//!   `drop_glue_std_container_still_open.rs` gap, not this file's subject).
//!
//! Paired with `..._default_global_discharges.rs` (no allocator: must NOT
//! refuse) and `..._panic_free_user_dealloc_still_refused.rs` (the slice's
//! documented stopping point). Neither direction is meaningful alone.
use std::alloc::{GlobalAlloc, Layout};

pub struct PanickyAlloc;

unsafe impl GlobalAlloc for PanickyAlloc {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        core::ptr::null_mut()
    }
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        //~^ ERROR Trust Level 0 safety verification incomplete
        //~| ERROR Trust strict verification failed
        panic!("dealloc panics");
    }
}

#[global_allocator]
pub static A: PanickyAlloc = PanickyAlloc;
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
