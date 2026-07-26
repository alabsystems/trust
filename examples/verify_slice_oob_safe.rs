// Trust test: fixed-size slice access -- safe variant (no obligation row)
// VcKind: IndexOutOfBounds
// Expected: IndexOutOfBounds ABSENT
// The constant-index bounds check (`data[0]` into `[u32; 1]`) is statically
// discharged before transport (the type guarantees index 0 exists), so the
// build carries no bounds row at all — and under the typed grammar absence
// is not PROVED. ABSENT is a generation assertion, not a proof claim.
// The out-of-bounds refutation itself is alive and caught by the buggy pair
// verify_slice_oob.rs (SliceBoundsCheck FAILED).
// Safe pattern: use a one-element array reference when the function requires
// a first element.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn first_safe(data: &[u32; 1]) -> u32 {
    data[0] // SAFE: type guarantees index 0 exists
}

fn main() {
    let data = [1];
    let _ = first_safe(&data);
}
