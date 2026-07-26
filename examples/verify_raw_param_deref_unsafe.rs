// Trust test: raw-pointer deref of an arbitrary parameter -- unsafe variant
// VcKind: Assertion
// Expected: Assertion FAILED
// The assertion finding is the fail-closed catch for arbitrary-pointer validity.
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
