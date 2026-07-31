// Trust test: raw-pointer deref of a live-local reference -- conservative variant
// VcKind: Assertion { message: "[unsafe...]" } -- transports as the hardened
//   unsafe-operation family (`hardened_unsafe_operation`), not `assert`.
// Expected: HardenedBoundary(UnsafeOperation) PROVED AND HardenedBoundary(UnsafeOperation) FAILED
// Current expectation: fail-closed. The deref of `p` is humanly-evidently sound, but
//   trustc deliberately refuses to certify it: at the MIR extraction point all
//   StorageLive/StorageDead markers are erased, so this body is shape-identical
//   to its dangling twin (verify_raw_ref_deref_dangling_unsafe) -- any lane that
//   proved this one would prove the dangling one too. The decisive rows are the
//   two `Formula::Bool(true)` design mandates -- the SAFETY-doc mandate and the
//   [unsafe:sep:addr_of] source-liveness mandate (always CAUGHT since
//   447e3e5441d) -- which are unprovable by construction, plus the unmodeled
//   rustc ub-check asserts (align/null, trust.vc::unsupported_mir catch-all).
//   The narrow non-null fact the stack-good lane discharges (`ptr == 0` refuted
//   for the address of a local) is a genuine proof and is deliberately left
//   alone by `refute_unsafe_demand_findings`; the PROVED token above pins that
//   spared discharge (the pre-fix blanket override destroyed it and ICEd the
//   positive-witness assertion, so this header could not pass at all). It
//   proves nothing about liveness, which is what this file is about; the
//   FAILED token pins the mandates. Exit 1 is the honest verdict; this file
//   pins that the conservatism holds. Renamed from *_safe: the trust-extra lane
//   derives an exit-0 contract from the _safe suffix, which this file can not
//   soundly meet.
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
