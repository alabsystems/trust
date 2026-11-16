//@ probe-shape: ComparisonBool
//@ probe-expect: discharged
//@ probe-note: POSITIVE since the BitVec.ofNat multi-limb/OfNat lift in
//@ probe-note: first-party/clean (05f6b0b3d). This file was born as a NEGATIVE
//@ probe-note: (f43_NEG_island_numeral_below_2p64): a numeral written in an island
//@ probe-note: was definitionally equal to the literal trustc mints only when its
//@ probe-note: VALUE was at least 2^64 or spelled `Nat.zero` (f34), because the
//@ probe-note: kernel's `reduce_bitvec_of_nat` read its operand through a u64-capped
//@ probe-note: bare-literal reader: it FIRED on the mint's small bare literal and
//@ probe-note: PARKED on the island's OfNat-wrapped spelling, so the two normal
//@ probe-note: forms diverged exactly below the threshold.
//@ probe-note:
//@ probe-note: The reducer now reads bare AND OfNat-wrapped Nat literals at any
//@ probe-note: magnitude up to 2^128-1 and emits the payload via the multi-limb
//@ probe-note: constructor, so `BitVec.ofNat 128 100` reduces to the same canonical
//@ probe-note: literal on both sides and this probe discharges. f44 is the same
//@ probe-note: probe on the other side of the old threshold; the pair now pins that
//@ probe-note: the MAGNITUDE NO LONGER DECIDES.
//@ probe-note:
//@ probe-note: What this bought a client: machine width guards whose bound is a
//@ probe-note: small positive literal became statable. The veripb kernel could cite
//@ probe-note: only the LOWER bound of its i64 width guard (i64::MIN at 128 bits is
//@ probe-note: 2^128 - 2^63, above the old threshold) and not the UPPER
//@ probe-note: (i64::MAX = 9223372036854775807, below it). Both halves are citable
//@ probe-note: now; the first client theorem over a sub-2^64 bound is
//@ probe-note: `guard_fits_upper_exact` in veripb-alab's island.
clean {
    def key128 (v : BitVec 128) : Nat :=
        Nat.xor (BitVec.toNat v) 170141183460469231731687303715884105728
    def bound_isl (x : BitVec 128) : Bool :=
        @Decidable.decide (Nat.le (key128 x) (key128 (BitVec.ofNat 128 100)))
                         (Nat.decLe (key128 x) (key128 (BitVec.ofNat 128 100)))
}
pub fn at_bound(x: i128) -> bool
    ensures result == bound_isl(x)
{ x <= 100 }
