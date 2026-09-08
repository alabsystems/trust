//@ probe-shape: ConstantInt
//@ probe-expect: defeq-rejected
//@ probe-flags: -O
//@ probe-note: The paired NEGATIVE for f58, and a DEFERRED ratchet.
//@ probe-note: The body returns `1`; the island says `0`. The claim is simply FALSE, so
//@ probe-note: if this ever discharges, a signed-constant mint has been accepted against
//@ probe-note: a value it does not compute — a soundness incident, not a test update.
//@ probe-note:
//@ probe-note: Today it CANNOT discharge, and not because the mint is right: it is
//@ probe-note: blocked by the same pre-existing clause-lane gap as f58 (a variable-less
//@ probe-note: atom defaults to the `Nat` domain, so the goal is ill-typed and refused
//@ probe-note: before defeq). So this row and f58 are currently INDISTINGUISHABLE by
//@ probe-note: verdict, and that is stated rather than hidden.
//@ probe-note:
//@ probe-note: THE RATCHET: f58 and f59 must stay PAIRED. The moment the constant clause
//@ probe-note: lane opens — a variable-less atom taking its carrier from the admission
//@ probe-note: instead of defaulting to `Nat` — f58 becomes `discharged` and this row
//@ probe-note: MUST become `defeq-rejected`. If f58 flips and f59 flips WITH it, the
//@ probe-note: defeq comparison is not discriminating on value and the widening is wrong.
//@ probe-note: Until then the live pin on wrong-value refusal is the trust-certify def-eq
//@ probe-note: oracle, which does reach the judgment and does refuse the forgeries.
//@ probe-note:
//@ probe-note: UPDATED 2026-08-26, E6/E9 widening increment 8
//@ probe-note: (typed-call argument/result carriers): the expectation
//@ probe-note: moved from `clause-outside-fragment` to `defeq-rejected`, and that is a
//@ probe-note: STRENGTHENING of this negative, not a weakening. Before, the wrong value was
//@ probe-note: never actually compared: the clause failed to type at all (the f04-f09 wall),
//@ probe-note: so the row proved nothing about values. Now the goal types, the two sides
//@ probe-note: meet, and the KERNEL refuses them — `BitVec.ofNat 64 1` is not
//@ probe-note: `BitVec.ofNat 64 Nat.zero`. Same direction, and for the first time for the
//@ probe-note: reason the row's name claims.
clean { def zero_isl : BitVec 64 := BitVec.ofNat 64 Nat.zero }
pub fn one_i64() -> i64
    ensures result == zero_isl()
{ 1 }
