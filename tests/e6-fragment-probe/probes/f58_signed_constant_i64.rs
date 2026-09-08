//@ probe-shape: ConstantInt
//@ probe-expect: discharged
//@ probe-flags: -O
//@ probe-note: SIGNED-CONSTANT ADMISSION — the body of the four `CoeffDomain`/`Exact`
//@ probe-note: `zero`/`one` impls of the veripb client, which were `admissible=true,
//@ probe-note: recognize=None` for one reason only: `AdmissibleBody::ConstantUint`
//@ probe-note: matched `ConstValue::Uint`, and a SIGNED literal extracts as
//@ probe-note: `ConstValue::Int(i128)` — sign-extended, and carrying NO width. The new
//@ probe-note: `ConstantInt` shape takes the width from the DECLARED return type instead
//@ probe-note: (pinned signed, and pinned to agree with `_0`'s own declared type) and
//@ probe-note: range-checks the value against it, so a literal can never be minted at a
//@ probe-note: carrier it does not fit.
//@ probe-note:
//@ probe-note: WHAT THIS ROW MEASURES is the E6 column, not the verdict: `recognize=`
//@ probe-note: flips from `None` to `ConstantInt`. The VERDICT is deliberately unchanged
//@ probe-note: at `clause-outside-fragment`, and that is a PRE-EXISTING clause-lane gap
//@ probe-note: this increment does not touch: no constant-shaped probe in this corpus
//@ probe-note: discharges (f04-f09), because a variable-less clause atom defaults to the
//@ probe-note: `Nat` domain and the `BitVec 64` island call then sits under an `Eq Nat`,
//@ probe-note: which the ill-typed-goal gate refuses before any defeq attempt. Exactly
//@ probe-note: f08's shape and exactly f08's verdict, one carrier over.
//@ probe-note:
//@ probe-note: The mint's SPELLING — the part that would be a wrong-verdict risk — is
//@ probe-note: therefore pinned where it can actually be checked: the trust-certify def-eq
//@ probe-note: oracle compares the mint against this same island text through the real
//@ probe-note: island elaborator, and refuses a wrong-VALUE twin (`-1` read as its
//@ probe-note: magnitude, MIN read as MAX) and a wrong-WIDTH twin. `0` must take
//@ probe-note: `Domain::zero`'s `Nat.zero` spelling, not `numeral(0)`; a negative must
//@ probe-note: take the two's-complement pattern.
//@ probe-note:
//@ probe-note: UPDATED 2026-08-26, E6/E9 widening increment 8
//@ probe-note: (typed-call argument/result carriers): the VERDICT above
//@ probe-note: has flipped from `clause-outside-fragment` to `discharged`, and the paragraph
//@ probe-note: below describing the f04-f09 wall is now HISTORY, not current behaviour. The
//@ probe-note: wall was the clause elaborator defaulting a variable-less atom to `Nat`; the
//@ probe-note: atom now takes the `Signed(I64)` domain this row's own mint recorded, and the
//@ probe-note: island's declared `BitVec 64` result carrier is checked against it. f04-f09
//@ probe-note: moved with it. f63 is the i128 twin; f59 is the wrong-value negative, which
//@ probe-note: is now refused by the KERNEL (`defeq-rejected`) rather than by a typing
//@ probe-note: accident that never let the two sides meet.
clean { def zero_isl : BitVec 64 := BitVec.ofNat 64 Nat.zero }
pub fn zero_i64() -> i64
    ensures result == zero_isl()
{ 0 }
