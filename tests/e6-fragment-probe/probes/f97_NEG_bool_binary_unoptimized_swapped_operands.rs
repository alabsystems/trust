//@ probe-shape: BoolBinary
//@ probe-expect: defeq-rejected
//@ probe-note: NEGATIVE, must stay red, and the CLOSE twin of f95: byte for
//@ probe-note: byte the same Rust body and the same island model except that
//@ probe-note: the SECOND leaf's operands are swapped -- the model says
//@ probe-note: `hi <= p` where the body computes `p <= hi`. Also without `-O`,
//@ probe-note: so it exercises the forwarded arm spelling f95 added.
//@ probe-note: Admitting a two-statement arm must not blur WHICH comparison
//@ probe-note: the arm holds: the arm's value is still read out of the
//@ probe-note: comparison statement, operand order and all, and the kernel
//@ probe-note: must refuse the constructed `Eq.refl`. If this ever discharges,
//@ probe-note: the widening has started reading arms positionally and f95/f96
//@ probe-note: are green for an accidental reason.
//@ probe-note: The forgery is deliberately the SOUND-LOOKING one: on an
//@ probe-note: interval where `lo = hi` the two models agree pointwise, so
//@ probe-note: only a real defeq check separates them.
clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    def axis_swapped_isl (p : BitVec 64) (lo : BitVec 64) (hi : BitVec 64) : Bool :=
        Bool.and (Decidable.decide (Nat.le (key64 lo) (key64 p))
                                   (Nat.decLe (key64 lo) (key64 p)))
                 (Decidable.decide (Nat.le (key64 hi) (key64 p))
                                   (Nat.decLe (key64 hi) (key64 p)))
}
pub fn axis_contains(p: i64, lo: i64, hi: i64) -> bool
    ensures result == axis_swapped_isl(p, lo, hi)
{ p >= lo && p <= hi }
