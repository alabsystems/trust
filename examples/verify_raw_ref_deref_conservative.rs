// Trust test: raw-pointer deref of a live-local reference -- conservative variant
// VcKind: Assertion
// Expected: Assertion UNKNOWN AND Assertion FAILED
// Current expectation: fail-closed. The deref of `p` is humanly-evidently sound, but
//   trustc deliberately refuses to certify it: at the MIR extraction point all
//   StorageLive/StorageDead markers are erased, so this body is shape-identical
//   to its dangling twin (verify_raw_ref_deref_dangling_unsafe) -- any lane that
//   proved this one would prove the dangling one too. Four rows fail closed by
//   design: the SAFETY-doc mandate (unknown), the [unsafe:sep:addr_of]
//   source-liveness design-mandate VC (Bool(true), always CAUGHT since
//   447e3e5441d), and the two unmodeled rustc ub-check asserts (align/null,
//   trust.vc::unsupported_mir catch-all). Exit 1 is the honest verdict; this
//   file pins that the conservatism holds. Renamed from *_safe: the trust-extra
//   lane derives an exit-0 contract from the _safe suffix, which this file can
//   not soundly meet.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn read_local() -> i32 {
    let x: i32 = 7;
    let p = &x as *const i32;
    // SAFETY: `p` points to the live local `x`, which is i32-aligned and in
    // bounds at offset 0. Stack-good provenance (no StorageDead on `x`, no loop).
    unsafe { *p }
}

fn main() {
    let _ = read_local();
}
