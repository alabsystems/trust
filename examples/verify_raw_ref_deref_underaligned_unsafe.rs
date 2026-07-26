// Trust test: raw-pointer deref under-aligned -- unsafe variant
// VcKind: Assertion
// Expected: Assertion FAILED
// The assertion finding is the fail-closed catch for insufficient alignment.
// Counterexample: a `u8` local is 1-byte aligned, but `*const u32` needs 4.
//
// Soundness guard: the stack-good lane discharges alignment ONLY when the
// backing local's alignment (here 1, for `u8`) is >= the deref pointee's
// required alignment (here 4, for `u32`). 1 < 4, so alignment stays caught.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn underaligned() -> u32 {
    let x: u8 = 7;
    let p = &x as *const u8 as *const u32;
    // BUG: `x` is only 1-byte aligned, but reading a u32 requires 4-byte alignment.
    unsafe { *p }
}

fn main() {
    let _ = underaligned();
}
