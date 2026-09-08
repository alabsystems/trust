//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-IS: `arr[i] = v` on an SSA-BOUND local array with a DYNAMIC index —
// pure value surgery, no memory: bounds `icmp ult` + `assert` (the FI-b
// typed `BoundsCheck` obligation row, `ProofAnnotation::InBounds`) then
// `insertelement` with the RUNTIME index value and a `set_local` rebind.
// MIR's own semantics are the bounds assert then the store, so an OOB index
// traps identically on both sides and the interpreter's own OOB arm is
// unreachable. Fences: the local is SSA-bound (promoted/borrowed arrays
// keep the fail-closed tag — their writes must go through memory), the
// mapped ty is `Ty::Array` with a known length, index and rhs are
// non-borrow-ptr values. Composes with wave-FR: the `for i in 0..n`
// SIMD-kernel shape lowers end to end, obligations included.

// The composed kernel shape (const-generics-simd's add_arrays family).
pub fn fill(n: u64) -> u64 {
    let mut result = [0u64; 8];
    for i in 0..8u64 {
        result[i as usize] = i * n;
    }
    result[3]
}

// Element-to-element with two arrays, both dynamic.
pub fn scale(k: i64) -> i64 {
    let src = [1i64, 2, 3, 4];
    let mut dst = [0i64; 4];
    for i in 0..4u64 {
        dst[i as usize] = src[i as usize] * k;
    }
    dst[2]
}

// A dynamic index from a parameter: the bounds obligation is REAL (i >= 4
// panics at runtime; the assert row carries exactly that claim).
pub fn set_at(i: usize, v: u8) -> u8 {
    let mut a = [0u8; 4];
    a[i] = v;
    a[0]
}
