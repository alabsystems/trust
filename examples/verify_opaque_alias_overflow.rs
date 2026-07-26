// examples/verify_opaque_alias_overflow.rs — Goal 3 (raise the proof floor):
// VcKind: ArithmeticOverflow { op: BinOp::Add }
// Expected: ArithmeticOverflow(Add) FAILED
// opaque / `impl Trait`-typed locals must no longer poison the whole
// function's verification.
//
// Before the alias-normalization change, the `acc` local below has type
// `impl Iterator<Item = usize>` (a `TyKind::Alias` of kind `Opaque`). The
// verifier's fast-reject saw the alias, returned `Unsupported` for the
// ENTIRE function, and emitted ZERO proof obligations — including for the
// genuinely-overflowing `a + b` in `sum_with_offset`.
//
// After the change, `trust-mir-extract` reveals the opaque to its concrete
// underlying iterator type (rustc's own PostAnalysis normalization), the
// local gets a real `Sort`, and the overflow obligation on `a + b` is
// generated again — so Trust reports the overflow (or proves it absent in
// the `_safe` variant) instead of silently skipping the function.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Returns an `impl Iterator` (opaque/RPIT). The returned local's type is
/// a `TyKind::Alias { Opaque }` in MIR.
fn offsets(base: usize) -> impl Iterator<Item = usize> {
    (0..4).map(move |i| base + i)
}

/// `acc` is typed by the opaque above. The `a + b` add can overflow for
/// large inputs — Trust must now generate an overflow obligation here
/// (it could not while the opaque local poisoned the function).
fn sum_with_offset(a: usize, b: usize) -> usize {
    let mut acc = offsets(a); // local typed `impl Iterator<Item = usize>`
    let first = acc.next().unwrap_or(0);
    a + b + first
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len();
    let _ = sum_with_offset(n, n);
}
