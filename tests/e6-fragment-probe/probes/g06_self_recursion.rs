//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: Direct self-recursion. `facets.rs` refuses Total on any back-edge and
//@ probe-note: `verify_output::eval_block` fails closed on one, so recursion is refused by
//@ probe-note: the verification lane and not only by the body recognizer. The kernel's
//@ probe-note: infer_type/whnf/is_def_eq are mutually recursive, so this is the deepest
//@ probe-note: of the structural blockers.
//@ probe-note: First measured `unproved` at c4e667ca51; current 4c8a1e19da reports
//@ probe-note: `ClauseOutsideFragment`. Both refuse before defeq; the current explicit
//@ probe-note: classification is the fail-closed verdict pinned by this header.
clean { def zero_isl : UInt64 := 0 }
pub fn countdown(x: u64) -> u64
    ensures result == zero_isl
{ if x == 0 { 0 } else { countdown(x.wrapping_sub(1)) } }
