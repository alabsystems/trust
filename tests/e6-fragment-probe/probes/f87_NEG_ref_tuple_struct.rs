//@ probe-shape: Projection
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red until owner ruling R5b (`self.0` for a tuple
//@ probe-note: struct). MEASURED, and it is the half of this shape that was NOT obvious.
//@ probe-note: `Tup(u32, u32)` IS a struct, IS `Freeze`, and its declared field NAMES are
//@ probe-note: `"0"` and `"1"`, which are in the scalar vocabulary — so the signature scan
//@ probe-note: admits it and the view really MINTS, with rows `t.0`/`t.1`
//@ probe-note: (`TRUST_E6_DEBUG` prints `MINTED ... params=["t.0", "t.1"]`). What refuses
//@ probe-note: the program is the CLAUSE side: the elaborator supports only a depth-1
//@ probe-note: NAMED field projection, so `t.0` is outside the fragment and says so in its
//@ probe-note: own words. Fail-closed, with an accurate message, and the cost is one
//@ probe-note: unnameable constant in the kernel environment — recorded rather than
//@ probe-note: papered over, because the tempting "fix" (refuse tuple structs in the scan)
//@ probe-note: would replace a precise diagnostic with a vaguer one.
//@ probe-note: WHEN R5b LANDS this row flips, and the same commit owes a mutation control
//@ probe-note: that the index the clause names is the index the body reads — the tuple
//@ probe-note: analogue of `f73`.
clean { def id32tp (x : UInt32) : UInt32 := x }
pub struct Tup(pub u32, pub u32);
pub fn first(t: &Tup) -> u32
    ensures result == id32tp(t.0)
{ t.0 }
