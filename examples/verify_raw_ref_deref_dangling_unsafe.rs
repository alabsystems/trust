// Trust test: raw-pointer deref of a dangling local -- unsafe variant
// VcKind: Assertion
// Expected: Assertion FAILED
// The assertion finding is the fail-closed catch for the use-after-end.
// Counterexample: `x`'s storage ends before `*p`, so `p` dangles.
//
// Soundness guard: the backing local `x` has a `StorageDead` (its scope ends
// before the deref), so it is NOT stack-good — the deref stays fail-closed.
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
