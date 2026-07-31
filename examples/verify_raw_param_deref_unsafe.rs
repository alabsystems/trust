// Trust test: raw-pointer deref of an arbitrary parameter -- unsafe variant
// VcKind: Assertion { message: "[unsafe...]" } -- transports as the hardened
//   unsafe-operation family (`VcKind::transport_tag` routes every kind with a
//   `hardened_category()` through `hardened_<category>`, so these rows are
//   `hardened_unsafe_operation`, never `assert`).
// Expected: HardenedBoundary(UnsafeOperation) FAILED
// The unsafe-demand finding is the fail-closed catch for arbitrary-pointer validity.
// Counterexample: the caller may pass any pointer (null, dangling, misaligned).
//
// Soundness guard: `p` is a function parameter with no `&local` provenance in
// this function, so it is never stack-good — the deref stays fail-closed.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn deref_param(p: *const i32) -> i32 {
    // BUG: `p` is an arbitrary caller-supplied pointer; its validity is unknown.
    unsafe { *p }
}

fn main() {
    let x: i32 = 7;
    let _ = deref_param(&x as *const i32);
}
