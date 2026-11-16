//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//! REGRESSION (2026-09-20): the `&&`-of-two-comparisons body discharges
//! WITHOUT `-O`.
//!
//! `TrustVerify` is the last pass of `run_optimization_passes`, so the E6 body
//! recognizers read post-pipeline MIR — and `sess.mir_opt_level()` is 1 without
//! `-O` and 2 with it. At level 2 `DestinationPropagation` coalesces the RHS
//! comparison of a short-circuit `&&` straight into the shared arm place; at
//! level 1 it does not, and MIR building's forwarding temp survives:
//!
//! ```text
//! bb1: { _6 = Le(copy _1, copy _3); _4 = copy _6; goto -> bb3; }   // no -O
//! bb1: { _4 = Le(copy _1, copy _3);               goto -> bb3; }   // -O
//! ```
//!
//! `bool_binary_arm` accepted only the second spelling, so this body reported
//! ``ensures discharge requires the specified function … to be E6-admitted …;
//! it is not`` in every build without `-O` — including `targo trust check
//! FILE.rs`, the single-file lane, which reaches the recognizer at
//! `mir-opt-level 1` (measured on `379912412`: that lane answered `Gate: FAIL
//! [strict lane, exit 1]` on this body). **This fixture carries no
//! `-O` in its `compile-flags` on purpose**: add one and it stops testing
//! anything (`tests/e6-fragment-probe/probes/f45_bool_binary_and_i64.rs` is the
//! `-O` lane). The body is a3d-kernel's `axis_contains` verbatim.
//!
//! `>=` normalizes by SWAPPING its operands, never by negation, so the model's
//! first leaf reads `lo <= p`.

clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    def axis_within_isl (p : BitVec 64) (lo : BitVec 64) (hi : BitVec 64) : Bool :=
        Bool.and (@Decidable.decide (Nat.le (key64 lo) (key64 p))
                                   (Nat.decLe (key64 lo) (key64 p)))
                 (@Decidable.decide (Nat.le (key64 p) (key64 hi))
                                   (Nat.decLe (key64 p) (key64 hi)))
}

fn axis_contains(p: i64, lo: i64, hi: i64) -> bool
    ensures result == axis_within_isl(p, lo, hi)
{
    p >= lo && p <= hi
}

fn main() {
    let _ = axis_contains(1, 0, 2);
}
