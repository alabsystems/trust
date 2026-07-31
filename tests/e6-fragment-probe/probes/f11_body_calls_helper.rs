//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: Unknown-callee negative control. Exact certified same-unit callees can
//@ probe-note: participate in facet closure; this helper has no E6 admission, so its
//@ probe-note: caller must not borrow purity/totality authority from the function name.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub fn helper(x: u64) -> u64 { x }
pub fn caller(x: u64) -> u64
    ensures result == ident_isl(x)
{ helper(x) }
