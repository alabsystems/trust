//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify
//@ check-pass
//@ dont-check-compiler-stderr
#![feature(core_intrinsics)]
#![allow(internal_features)]
//! **`intrinsics::wrapping_add` IS MODULAR — and a plain `+` still is not.**
//!
//! # What was wrong
//!
//! `rustc_mir_transform::lower_intrinsics` rewrites
//! `intrinsics::wrapping_{add,sub,mul}` into a bare
//! `Rvalue::BinaryOp(Add|Sub|Mul, ..)`. That is the correct MIR — plain integer
//! `Add` IS defined wrapping — but it is also *exactly* what a source-level `+`
//! lowers to once overflow checks are off, so after the pass the two are
//! indistinguishable. Measured with the pre-fix stage2 `trustc`
//! (`rustc 1.99.0-dev (ccf52b40c 2026-08-19)`), `-Coverflow-checks=off`, the
//! extracted MIR for `a + b` and for `intrinsics::wrapping_add(a, b)` is the
//! byte-identical `BinaryOp("Add", Copy(_1), Copy(_2))`.
//!
//! Trust therefore charged the modular operation a no-overflow obligation, and
//! it FAILED with the counterexample `a = 4294967295, b = 1` — a refutation of
//! an operation that cannot overflow by definition. It is what makes
//! `core::num`'s whole `wrapping_*` family unverifiable (3 of the 43 failing
//! obligations in the `core::num` leaf slice,
//! `docs/design/2026-08-20-core-slice-blocker-histogram.md` §2.1).
//!
//! # The fix, and why it lives where it does
//!
//! The wrapping identity cannot be recovered downstream, so it is carried from
//! the pass that destroys it: `LowerIntrinsics` stamps
//! `mir::Statement::trust_modular_arith`, `trust_verify::trust_modular_arith_ops`
//! reads it off the very body it verifies and installs the `(span, op)` set on
//! the `VcgenContext`, and `generate::safety` withholds the obligation for
//! exactly those operations.
//!
//! # What this fixture pins
//!
//! `check-pass` under `-Ztrust-policy=certify` — the STRICT policy, under which
//! any failed, unknown, timed-out or runtime-checked obligation is a build
//! error. So it is a positive statement about all four functions below at once:
//! the three modular ops are certified with no residue.
//!
//! The other direction — that a plain `+` in the same shape is STILL charged —
//! is the more important half and is pinned by
//! `wrapping_intrinsic_plain_add_still_charged.rs`, which must keep failing.
//! Unit-level, the pair is
//! `trust_vcgen::generate::modular_arith_certificate_tests`.

use core::intrinsics;

pub fn wrap_add(a: u32, b: u32) -> u32 {
    intrinsics::wrapping_add(a, b)
}

pub fn wrap_sub(a: u32, b: u32) -> u32 {
    intrinsics::wrapping_sub(a, b)
}

pub fn wrap_mul(a: u32, b: u32) -> u32 {
    intrinsics::wrapping_mul(a, b)
}

/// The `unchecked_*` family sits in the SAME `LowerIntrinsics` arm but is UB on
/// overflow, not modular, and is deliberately NOT certified. It is absent from
/// this file on purpose: were it flagged, this fixture would keep passing and
/// silently document a real obligation removed.
fn main() {}
