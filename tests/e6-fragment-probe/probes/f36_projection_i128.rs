//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: The i128 width table opens the OTHER shapes too, not just the comparison
//@ probe-note: one: this is the plain projection at `BitVec 128`, stated against a
//@ probe-note: hand-written island definition, so the probe also pins that an author can
//@ probe-note: SPELL the 128-bit carrier. f13 is the paired negative — an island stated
//@ probe-note: at the wrong carrier still fails the ill-typed-goal gate, at any width.
clean { def ident_w (x : BitVec 128) : BitVec 128 := x }
pub fn idw(x: i128) -> i128
    ensures result == ident_w(x)
{ x }
