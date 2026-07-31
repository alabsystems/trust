// Trust test: raw-pointer deref loop-carried (under-free) -- unsafe variant
// VcKind: Assertion { message: "[unsafe...]" } -- transports as the hardened
//   unsafe-operation family (`hardened_unsafe_operation`), not `assert`.
// Expected: HardenedBoundary(UnsafeOperation) FAILED
// The unsafe-demand finding is the fail-closed catch for the loop-carried dangle.
// Counterexample: `p` holds the PREVIOUS iteration's `&x`, whose local `x`
//   has already been dropped at the loop back-edge.
//
// Soundness guard (the decisive one): the function has a back-edge (the
// `while` loop), so NO provenance is stack-good — this is immune to the
// MIR-index-ordered, path-insensitive walk that would otherwise visit the
// back-edge `StorageDead` AFTER the deref and false-prove the under-free.
// If this ever VERIFIES, the whole-program gate is broken.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn loop_carried(n: usize) -> i32 {
    let mut acc: i32 = 0;
    let mut p: *const i32 = core::ptr::null();
    let mut i: usize = 0;
    while i < n {
        let x: i32 = i as i32;
        let q = &x as *const i32;
        if i > 0 {
            // BUG: `p` points to the PREVIOUS iteration's `x`, already dead.
            acc = acc.wrapping_add(unsafe { *p });
        }
        p = q;
        i += 1;
    }
    acc
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len();
    let _ = loop_carried(n);
}
