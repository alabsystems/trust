//@ probe-shape: Arithmetic
//@ probe-expect: clause-outside-fragment
//@ probe-note: STRUCTURAL CONTRADICTION. The Arithmetic shape is BUILT from a
//@ probe-note: wrapping_add CALL, but the facet gate poisons on any Terminator::Call
//@ probe-note: (facets.rs:261). So the recognizer matches and admission still refuses:
//@ probe-note: shapes S3 and S4 are unreachable. Unblocking this is charter item 8.
clean { def winc_isl (x : UInt64) : UInt64 := x + 1 }
pub fn winc(x: u64) -> u64
    ensures result == winc_isl(x)
{ x.wrapping_add(1) }
