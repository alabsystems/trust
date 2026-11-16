//@ probe-shape: BoolBinary
//@ probe-expect: discharged
//@ probe-note: f95's disjunction twin, also WITHOUT `-O`. For `||` the
//@ probe-note: short-circuit constant `true` sits on the `otherwise` arm and
//@ probe-note: the second comparison on the `0` arm, so it is the OTHER arm
//@ probe-note: that forwards through a temp -- measured 2026-09-20 on
//@ probe-note: 379912412: `bb1: { _6 = Gt(copy _1, copy _3); _4 = copy _6; }`
//@ probe-note: with `bb2: { _4 = const true; }`. Pinning both connectives
//@ probe-note: stops the widening from being an `&&`-only accident, and shows
//@ probe-note: that only the COMPARISON arm ever takes the forwarded
//@ probe-note: spelling: MIR building writes the constant straight into the
//@ probe-note: shared place, and a two-statement CONSTANT arm stays refused.
//@ probe-note: `>` normalizes by operand swap, so the model reads `hi < p`.
clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    def axis_outside_isl (p : BitVec 64) (lo : BitVec 64) (hi : BitVec 64) : Bool :=
        Bool.or (Decidable.decide (Nat.lt (key64 p) (key64 lo))
                                  (Nat.decLt (key64 p) (key64 lo)))
                (Decidable.decide (Nat.lt (key64 hi) (key64 p))
                                  (Nat.decLt (key64 hi) (key64 p)))
}
pub fn axis_outside(p: i64, lo: i64, hi: i64) -> bool
    ensures result == axis_outside_isl(p, lo, hi)
{ p < lo || p > hi }
