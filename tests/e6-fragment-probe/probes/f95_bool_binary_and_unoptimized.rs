//@ probe-shape: BoolBinary
//@ probe-expect: discharged
//@ probe-note: NO `probe-flags: -O`, and that is the whole point. f45 and f46
//@ probe-note: are the same lane WITH `-O`; this pair is the regression
//@ probe-note: fixture for the un-coalesced arm spelling. Without `-O` the
//@ probe-note: pipeline stops at `mir-opt-level = 1`, `DestinationPropagation`
//@ probe-note: does not run, and MIR building's forwarding temp survives into
//@ probe-note: the `TrustVerify` input -- measured 2026-09-20 on 379912412:
//@ probe-note: `bb1: { _6 = Le(copy _1, copy _3); _4 = copy _6; goto -> bb3; }`
//@ probe-note: where `-O` leaves `bb1: { _4 = Le(copy _1, copy _3); ... }`.
//@ probe-note: Until `bool_binary_arm` admitted the two-statement arm this
//@ probe-note: reported `clause-outside-fragment` with "requires the specified
//@ probe-note: function to be E6-admitted ...; it is not", which made the
//@ probe-note: `&&`-of-two-comparisons shape UNREACHABLE through the
//@ probe-note: single-file lane: measured on 379912412, `targo trust check
//@ probe-note: main.rs` on this body answered `Gate: FAIL [strict lane, exit
//@ probe-note: 1] (1 proved, ... 2 unknown / 3 total)`.
//@ probe-note: The body is a3d-kernel's `axis_contains` verbatim: three
//@ probe-note: parameters, inclusive AABB containment on one axis. `>=`
//@ probe-note: normalizes by SWAPPING its operands, never by negation, so the
//@ probe-note: model's first leaf reads `lo <= p`.
clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    def axis_within_isl (p : BitVec 64) (lo : BitVec 64) (hi : BitVec 64) : Bool :=
        Bool.and (@Decidable.decide (Nat.le (key64 lo) (key64 p))
                                   (Nat.decLe (key64 lo) (key64 p)))
                 (@Decidable.decide (Nat.le (key64 p) (key64 hi))
                                   (Nat.decLe (key64 p) (key64 hi)))
}
pub fn axis_contains(p: i64, lo: i64, hi: i64) -> bool
    ensures result == axis_within_isl(p, lo, hi)
{ p >= lo && p <= hi }
