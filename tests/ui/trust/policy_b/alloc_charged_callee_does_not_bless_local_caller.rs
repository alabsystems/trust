//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Round-2 refutation of the 2026-09-16 allocation-side charge (recorded in
//! `docs/design/2026-07-25-completeness-gap-policy-ruling.md`, amendment
//! 2026-09-16): the publication seam charged `allocates_and_forgets` the
//! REFUSED `contract:global-alloc-dealloc-panic-free` row (a user
//! `#[global_allocator]` whose `alloc` panics is in the graph, and the body
//! makes a non-local call), while the interprocedural registry gate still asked
//! only about allocation-owning DROPS — so the same body, refused on the wire,
//! was registered unconditionally panic-free, and `calls_it` (whose only call is
//! local) was blessed `no_obligations: proved` on its strength.
//!
//! Now one detector (`body_is_charged_global_alloc_contract`) decides the seam,
//! the registry gate and R40 candidacy together: the charged callee is NOT
//! registered, so the caller's call is undischarged and it is refused too.
//!
//! The allocator's OWN bodies stay charged — `ff041d4b0c` pinned that
//! deliberately ("so the widening cannot be silently reverted"), and this file
//! follows its convention: the allocator impl and the four `#[global_allocator]`
//! expansion shims take `dont-require-annotations: ERROR` rather than a
//! positional transcription of every same-line error, because their count is not
//! this file's subject. What is pinned is the pair that is: the charged callee's
//! own refusal, and the local caller's.
use std::alloc::{GlobalAlloc, Layout};

pub struct PanicOnAlloc;

unsafe impl GlobalAlloc for PanicOnAlloc {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        panic!("alloc panics");
    }
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

#[global_allocator]
pub static A: PanicOnAlloc = PanicOnAlloc;

/// Allocates through the user allocator and never drops: no allocation-owning
/// drop, so the drop-side charge alone never fired here. The allocation side
/// charges it.
pub fn allocates_and_forgets() {
    //~^ ERROR the `contract:global-alloc-dealloc-panic-free`
    let s = String::from("x");
    std::mem::forget(s);
}

/// Its only call is LOCAL, so the allocation-side charge does not fire on this
/// body — its panic-freedom rests entirely on the callee being registered,
/// which the charged callee no longer is.
pub fn calls_it() {
    //~^ ERROR Trust strict verification failed
    allocates_and_forgets();
}
