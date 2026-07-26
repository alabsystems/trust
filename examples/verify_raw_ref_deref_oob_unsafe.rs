// Trust test: raw-pointer deref out of bounds -- unsafe variant
// VcKind: Assertion
// Expected: Assertion FAILED
// The assertion finding is the fail-closed catch for the out-of-bounds deref.
// Counterexample: `p.add(5)` is 5 elements past a single-`i32` allocation.
//
// Soundness guard: the stack-good lane discharges in-bounds ONLY at offset 0,
// so an offset pointer must never be falsely proved.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn oob() -> i32 {
    let x: i32 = 7;
    let p = &x as *const i32;
    // BUG: offset 5 is out of bounds — `x` is a single i32.
    unsafe { *p.add(5) }
}

fn main() {
    let _ = oob();
}
