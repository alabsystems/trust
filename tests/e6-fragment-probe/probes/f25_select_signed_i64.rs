//@ probe-shape: Select
//@ probe-expect: discharged
//@ probe-note: E6 WIDENING INCREMENT 4 — the SIGNED select (2026-08-23). Before it,
//@ probe-note: `ty_to_domain` failed closed on every `signed: true` type and this probe's
//@ probe-note: clause was clause-outside-fragment; f13 records where the rest of the
//@ probe-note: signed lane still is. The i64 carrier is the exact two's-complement
//@ probe-note: `BitVec 64`, and the mint's decision is stated over the SAME sign-flip
//@ probe-note: order keys the goal builder uses: `Nat.xor (BitVec.toNat v) 2^63`. The
//@ probe-note: island spells those keys out (the unsigned natural spelling
//@ probe-note: `if a < b then a else b` is deliberately NOT minted here — Clean's BitVec
//@ probe-note: order instances are unsigned, and reusing them would give the program's
//@ probe-note: signed `<` an unsigned meaning at i64::MIN). TRUST_E9_DEBUG prints the
//@ probe-note: goal to copy the key spelling from; a named island helper (`key64`, see
//@ probe-note: the e9_min2_i64 ui pair) is the readable authoring shape.
clean {
    def min2_isl (a : BitVec 64) (b : BitVec 64) : BitVec 64 :=
        if Nat.lt (Nat.xor (BitVec.toNat a) 9223372036854775808)
                  (Nat.xor (BitVec.toNat b) 9223372036854775808) then a else b
}
pub fn min2(a: i64, b: i64) -> i64
    ensures result == min2_isl(a, b)
{ if a < b { a } else { b } }
