//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: The same Call restriction seen from ordinary code: a body that calls
//@ probe-note: ANY function cannot be admitted, which excludes almost all real Rust.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub fn helper(x: u64) -> u64 { x }
pub fn caller(x: u64) -> u64
    ensures result == ident_isl(x)
{ helper(x) }
