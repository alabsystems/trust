// Trust test: raw-pointer deref of a dangling local -- unsafe variant
// VcKind: Assertion { message: "[unsafe...]" } -- transports as the hardened
//   unsafe-operation family (`hardened_unsafe_operation`), not `assert`.
// Expected: HardenedBoundary(UnsafeOperation) FAILED
// The unsafe-demand finding is the fail-closed catch for the use-after-end.
// Counterexample: `x`'s storage ends before `*p`, so `p` dangles.
//
// Soundness guard: the `[unsafe:sep:addr_of] &raw const on ... (source liveness
// unverified)` obligation is a `Formula::Bool(true)` design mandate emitted for
// EVERY address-of, so it is unprovable by construction and this deref stays
// fail-closed no matter what the separation lanes discharge. That is the
// load-bearing guard here: StorageLive/StorageDead markers are ERASED at MIR
// extraction, so `SepEngine::with_stack_good_gate` cannot see this local's
// `StorageDead` and the body is shape-identical to its live twin
// (verify_raw_ref_deref_conservative). The narrow facts the stack-good lane can
// still discharge -- "the address of a local is non-null" -- hold for a dangling
// pointer too, so a `hardened_unsafe_operation` proved row for the null check is
// sound; liveness itself is never proved.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn dangling() -> i32 {
    let p: *const i32;
    {
        let x: i32 = 7;
        p = &x as *const i32;
    } // `x`'s storage ends here (StorageDead) — `p` now dangles.
    // BUG: use-after-end; `p` points to a local whose storage has ended.
    unsafe { *p }
}

fn main() {
    let _ = dangling();
}
