//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: `match` on a USER enum, isolated against f18 (match on bool, refused).
//@ probe-note: f18 shows even a two-arm bool match is outside the five shapes; this pins
//@ probe-note: the ADT case separately, because widening bool-match would NOT reach it.
//@ probe-note: clean-kernel is 2,903 match expressions, nearly all over user ADTs.
//@ probe-note: First measured `unproved` at c4e667ca51; current 4c8a1e19da reports
//@ probe-note: `ClauseOutsideFragment`. Both refuse before defeq; the current explicit
//@ probe-note: classification is the fail-closed verdict pinned by this header.
clean { def one_isl : UInt64 := 1 }
pub enum E { A, B }
pub fn tag(e: E) -> u64
    ensures result == one_isl
{ match e { E::A => 1, E::B => 1 } }
