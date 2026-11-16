//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
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
//!
//! RE-PINNED 2026-09-16 for `2284569485`, which CHARGES the
//! `contract:global-alloc-dealloc-panic-free` caller contract on the ALLOCATION
//! side as well as the drop side. Its own body predicted this
//! ("the refuters' p3b_string37_forget.rs and p4c_box_u64_into_raw.rs refuse on
//! the stage1 rebuild, having built before") and it did not re-measure these two
//! files. The new rows are `<PanickyAlloc as GlobalAlloc>::alloc` and the
//! `__rust_alloc`/`__rust_realloc`/`__rust_alloc_zeroed` shims: a body that makes
//! a non-local call while the crate graph registers a user allocator is now
//! charged, because the allocator is a process-global channel into user code
//! from every allocating sysroot routine, not only from a drop.
//!
//! `dont-require-annotations: ERROR` is added rather than enumerating twelve
//! same-line shim errors positionally. The count on the `#[global_allocator]`
//! static was never this file's subject — its own comment calls those the
//! "MEASURED pre-existing baseline" — and a positional list of twelve is a
//! transcription, not a pin. What IS pinned stays explicit and grows by one: the
//! `drops_vec` refusal this file exists for, and now the allocation-side refusal
//! on `alloc`, so the 2026-09-16 widening cannot be silently reverted.
use std::alloc::{GlobalAlloc, Layout};

pub struct PanickyAlloc;

unsafe impl GlobalAlloc for PanickyAlloc {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
    //~^ ERROR the `contract:global-alloc-dealloc-panic-free` caller contract is refused
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
    // RE-PINNED 2026-09-21 (W3). This fn line now carries ONE diagnostic, the
    // contract refusal. The L0 header (WARN) and the obligation-count strict
    // error came from the bare `Vec`'s drop-glue row being UNPROVED; `Ty::Seq`
    // now carries the `AdtAuth::TotalDrop` stamp its ADT siblings always had,
    // so that row is proved and those two no longer fire. Comment kept at
    // SEVEN lines so the caret count below is unchanged -- annotations sit
    // directly under the fn line, one caret per line, no arithmetic.
    //~^^^^^^^^ ERROR the `contract:global-alloc-dealloc-panic-free`
    // THE PROPERTY THIS FIXTURE EXISTS FOR IS UNTOUCHED: a panicking user
    // `dealloc` is STILL refused, because a registered `#[global_allocator]`
    // replaces the dealloc chain with unverified code and no lane verifies it.
    // Measured after W3 -- this file still exits 1, and `String` /
    // `Option<Vec<u8>>`, which carried the stamp all along, refuse identically.
    // `Vec` became CONSISTENT with them, not newly permissive.
    v.len()
}
