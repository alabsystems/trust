//@ probe-shape: ConstantInt
//@ probe-expect: discharged
//@ probe-flags: -O
//@ probe-note: THE CONSTANT WALL, FALLING — the clause half of the signed-constant lane,
//@ probe-note: at the width f58 does not cover. f58 minted correctly and still reported
//@ probe-note: `clause-outside-fragment`, and its header named the reason exactly: "a
//@ probe-note: variable-less clause atom defaults to the `Nat` domain and the `BitVec 64`
//@ probe-note: island call then sits under an `Eq Nat`, which the ill-typed-goal gate
//@ probe-note: refuses before any defeq attempt". That was never a fact about constants;
//@ probe-note: it was the clause elaborator taking an atom's domain from its VARIABLES
//@ probe-note: (or, with none, from a default) instead of from the DECLARED signature of
//@ probe-note: the thing being applied — the same root cause as f60's mixed-width refusal.
//@ probe-note:
//@ probe-note: WHERE THE DOMAIN NOW COMES FROM, and why it is not a guess. The atom
//@ probe-note: `one_i128() == one_isl()` has no variables, so the elaborator asks the
//@ probe-note: admitted calls in it. `one_i128`'s admission is a compiler MINT, and a
//@ probe-note: mint records the exact `Domain` it built its declaration at — here
//@ probe-note: `Signed(I128)`. That is the ORIGINAL, not a re-derivation. The ISLAND
//@ probe-note: contributes nothing to the answer: its `BitVec 128` codomain has THREE
//@ probe-note: `Domain` preimages (`i128`, and `usize`/`isize` at that width would too at
//@ probe-note: 64), which is exactly the non-injectivity `island_definition_signature`
//@ probe-note: documents, so reading a domain off it is forbidden. What the island DOES
//@ probe-note: contribute is a CHECK: its declared result carrier must equal the carrier
//@ probe-note: the mint's domain names, and a disagreement is a named refusal rather than
//@ probe-note: a coercion. An island-only atom with no mint on either side therefore
//@ probe-note: still defaults to `Nat` and still fails closed — the widening is exactly
//@ probe-note: as wide as the authority behind it.
//@ probe-note:
//@ probe-note: THE VALUE IS PINNED ELSEWHERE, not by this row's green: the trust-certify
//@ probe-note: def-eq oracle compares the mint against this island text through the real
//@ probe-note: island elaborator and catches a wrong-VALUE twin (`-1` read as its
//@ probe-note: magnitude, MIN read as MAX) and a wrong-WIDTH twin. f59 is the in-corpus
//@ probe-note: negative: same island constant, a Rust body returning `1` instead of `0`,
//@ probe-note: and it now fails as `defeq-rejected` — refused by the KERNEL for having
//@ probe-note: the wrong value, rather than by a typing accident that never let the two
//@ probe-note: sides meet.
clean { def one_isl : BitVec 128 := BitVec.ofNat 128 1 }
pub fn one_i128() -> i128
    ensures result == one_isl()
{ 1 }
